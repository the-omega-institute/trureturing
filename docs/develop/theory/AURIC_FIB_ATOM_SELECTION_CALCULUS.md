# FIB-ATOM 选择项演算

金字塔的两条基本关系、递归接缝与完整读出

**约定 0.1（位置标签与论域）。** 选择项标记在 FIB 生成链上选取哪些位置。全卷使用 $`\mathsf{\text{𝖥}}_j[I]`$，其中 $`j\in\mathbb{\text{ℕ}}`$ 是窗口尺度，$`I`$ 是合法位置集合；零层简写为 $`\mathsf{\text{𝖥}}[I]`$。标准 Fibonacci 数另写作 $`\mathrm{Fib}_n`$，不与选择项混用。旧标签仅保留如下对应：

<table><tbody><tr><td>

```math
[null]=\mathsf{\text{𝖥}}[\varnothing],\qquad
[2]=\mathsf{\text{𝖥}}[1],\qquad
[3]=\mathsf{\text{𝖥}}[2],\qquad
[25]=\mathsf{\text{𝖥}}[1,3],\qquad
[5]=\mathsf{\text{𝖥}}[3].
```

</td></tr></tbody></table>

这里 $`\mathsf{\text{𝖥}}[1]`$ 选择当前窗口的第一位置，零层数量是二；它不是通常的 $`\mathrm{Fib}_1=1`$。括号内的 $`1,3`$ 表示集合 $`\{1,3\}`$，不表示十进制数十三。旧标签 $`[25]`$ 的零层数量是七，不是二十五。树来源、受限选择、组成坐标、概率律和已取得记录分别声明，不能因标签相同而互换。

**数学引文 0.2（固定来源与归属）。** 前五项正文取共同修订 [b8737c08f592e4df700978f25fb046d5a458f3c8](https://github.com/the-omega-institute/trureturing/tree/b8737c08f592e4df700978f25fb046d5a458f3c8)；末项只使用修订 [671ed2dcaf09d2f97799de233fc38e896911c248](https://github.com/the-omega-institute/trureturing/tree/671ed2dcaf09d2f97799de233fc38e896911c248) 的具名条款。简称在本卷保持固定。

| 简称及来源 | 本卷直接使用的范围 |
| --- | --- |
| [关系卷：FIB 关系延拓几何](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) | 定义 1.1、1.3，定理 1.2、1.4：有序树、替换、组成及数量；定义 3.1–3.3：任务的纤维下降；定义 7.1、定理 7.2：高到低即时数量读者与位权 |
| [基础卷：金字塔基础公式与原子关系](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) | 数学引文 2.2、3.2、4.2，§七：五函数代数、坐标金字塔、占位纤维与目标差分；§十一、数学引文 12.5：实际继续、取得边界及守卫计数 |
| [双曲卷：双曲几何与相位边界](AURIC_FIB_HYPERBOLIC_GEOMETRY_AND_PHASE_BOUNDARY.md) | 定义 7.1–7.2，定理 7.3、7.5、7.8：实际贡献、同源均值曲线、梯形及闭组成纤维、完整继续回复 |
| [关联卷：金字塔关联与原生接续](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md) | §§一–四：占位凸体和正方形核；定义 8.1–8.2、推导 8.3–8.5：扫描方向、因子化权重及开放端计数；定义 8.6、命题 8.7：跨窗联合障碍 |
| [行列式卷：金字塔行列式与原生守卫接续](AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md) | 定义 10.4、命题 10.5–10.6：实际首次奇偶记录、同历史继续、精确数量与未知概率律的区别 |
| [二阶卷：二阶关系完成](https://github.com/the-omega-institute/trureturing/blob/671ed2dcaf09d2f97799de233fc38e896911c248/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) | §§21、24：来源增长与实际尺度；§§101–103、106–107：明确 Pauli 乘序、所选代表和有条件的相干比较；命题 110.4：共同环境与新环境的区别 |

**约定 0.3（推导的角色）。** 五模式几何、既有概率纤维、原生守卫和已有回复表沿用上述来源，不把改写记号计作数学发现。本卷的 `repo-derived` 综合是：用固定基组成的四项一、二阶矩恢复单窗律，把它接到同历史立即继续的完整回复及奇偶条件任务，再用实际首次数量和随后空窗数量的统计给出另一条取得与消费桥。各桥只在声明的同一来源和操作合同内成立。几何的经典归属另见 [Stanley 的三元素 fence 与 chain polytope](../../../Library/Words/stanley1986posetpolytopes.md) 和 [Nigam–Phillips 的参考金字塔](../../../Library/Geometry/nigamphillips2007pyramids.md)；它们作为推导中的原料，不供应本卷的原生回复结论，也不规定物理空间。下文采用普通数学证明，不主张这些综合在世界文献中的优先权。

## 一、定义：选择的是位置，不是直接给一个数

**定义 1.1（原始 FIB 来源）。** 原始来源的载体是自由有序二叉树：

```math
\mathbb{\text{𝕋}}::=\alpha\mid\beta\mid\langle\mathbb{\text{𝕋}},\mathbb{\text{𝕋}}\rangle.
```

叶标签、左右顺序及全部括号都是来源的一部分。替换由以下完整规则唯一递归定义：

```math
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
```

令 $`T_n=\rho^n(\alpha)`$。关系卷定理 1.2 的结构递归在这里为

```math
T_0=\alpha,\qquad T_1=\beta=\rho(\alpha),
```

<table><tbody><tr><td>

```math
T_{n+2}=\langle T_{n+1},T_n\rangle\quad(n\ge0).
```

</td></tr></tbody></table>

证明。零层等式是替换对 $`\beta`$ 的规则；对等式施加保持有序配对的 $`\rho`$，得到下一层等式，归纳即成。特别地，

```math
T_2=\langle\beta,\alpha\rangle,\qquad
T_3=\langle\langle\beta,\alpha\rangle,\beta\rangle.
```

第三个轨道来源是复合树，不是第三种自由叶；只写 $`\beta=\rho(\alpha)`$ 而省略第二替换规则，不能确定这条生成链。

**定义 1.2（当前窗口的三个位置）。** 对每个非负整数 $`j`$，窗口的低、中、高三个位置对应

<table><tbody><tr><td>

```math
A_j=T_{3j},\qquad B_j=T_{3j+1},\qquad C_j=T_{3j+2},
\qquad C_j=\langle B_j,A_j\rangle.
```

</td></tr></tbody></table>

合法选择集合为三位置路径的独立集：

```math
\mathcal{\text{𝒮}}=\{I\subseteq\{1,2,3\}:I\text{ 不含相邻位置}\}.
```

选择项 $`\mathsf{\text{𝖥}}_j[I]`$ 是附有尺度和来源位置的模式，不自动指定任意组合的执行次序。选择关系与生成关系分别为

<table><tbody><tr><td>

```math
\text{选择关系：第一、第三位置能够共同出现；}
```

</td></tr></tbody></table>

<table><tbody><tr><td>

```math
\text{生成关系：第三位置由第二、第一位置有序组合生成。}
```

</td></tr></tbody></table>

**定理 1.3（局部合法选择的穷尽）。** 对定义 1.2，恰有

<table><tbody><tr><td>

```math
\mathcal{\text{𝒮}}=
\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}.
```

</td></tr></tbody></table>

证明。不选得到空集，单选有三个集合。双选中 $`\{1,2\}`$ 和 $`\{2,3\}`$ 含相邻位置，只有 $`\{1,3\}`$ 合法；三位置全选也含相邻位置。所有子集已分完，故恰有五项。∎

五模式由三个已有生成关系的位置及一项相邻排斥规则产生，并非增添五种自由原子。这一点也解释了为什么“第三位置由前两项生成”与“第一、第三位置可共同选择”能同时成立。

## 二、五个选择项怎样编译成原始树

**定义 2.1（选定的有序来源编译）。** 固定“高位置在左、低位置在右”的约定。对每个 $`j\ge0`$，定义

```math
\begin{aligned}
E_j[1]&=A_j,& E_j[2]&=B_j,& E_j[3]&=C_j,\\
E_j[1,3]&=\langle C_j,A_j\rangle.
\end{aligned}
```

这是 $`\mathcal{\text{𝒮}}\setminus\{\varnothing\}\to\mathbb{\text{𝕋}}`$ 的前向编译。另加一个空窗口贡献符号 $`\varepsilon_{\mathrm w}\notin\mathbb{\text{𝕋}}`$，令

```math
\mathbb{\text{𝕋}}_{\varnothing}=\mathbb{\text{𝕋}}\sqcup\{\varepsilon_{\mathrm w}\},\qquad
\widehat E_j[\varnothing]=\varepsilon_{\mathrm w},\qquad
\widehat E_j[I]=E_j[I]\quad(I\ne\varnothing).
```

空贡献不是一棵非空树，不是来源叶，也不是实际读者上的恒等动作。

**定义 2.2（组成、数量和固定基坐标）。** 按关系卷定义 1.3，组成是列向量，数量是线性读出：

```math
c(\alpha)=\begin{pmatrix}1\\0\end{pmatrix},\qquad
c(\beta)=\begin{pmatrix}0\\1\end{pmatrix},\qquad
c(\langle s,t\rangle)=c(s)+c(t),\qquad q=(2,3).
```

扩张组成读出令 $`\widehat c(\varepsilon_{\mathrm w})=0`$，在树上仍等于 $`c`$。固定基坐标定义为 $`d_I=\widehat c(\widehat E_0[I])`$。其表为

| 选择项 | 第 $`j`$ 窗口的代表 | 固定基组成 $`d_I`$ | 零层数量 $`qd_I`$ |
| --- | --- | --- | ---: |
| $`\mathsf{\text{𝖥}}_j[\varnothing]`$ | $`\varepsilon_{\mathrm w}`$ | $`(0,0)^{\mathsf{\text{𝖳}}}`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}_j[1]`$ | $`A_j`$ | $`(1,0)^{\mathsf{\text{𝖳}}}`$ | $`2`$ |
| $`\mathsf{\text{𝖥}}_j[2]`$ | $`B_j`$ | $`(0,1)^{\mathsf{\text{𝖳}}}`$ | $`3`$ |
| $`\mathsf{\text{𝖥}}_j[3]`$ | $`C_j=\langle B_j,A_j\rangle`$ | $`(1,1)^{\mathsf{\text{𝖳}}}`$ | $`5`$ |
| $`\mathsf{\text{𝖥}}_j[1,3]`$ | $`\langle C_j,A_j\rangle`$ | $`(2,1)^{\mathsf{\text{𝖳}}}`$ | $`7`$ |

该表的第三列固定在零层基架；它不是任意 $`j`$ 的实际两类叶数。第四节给出它到实际尺度组成的运输。

**命题 2.3（联合选择不是下一个 FIB 项）。** 在零层有

<table><tbody><tr><td>

```math
E_0[1,3]=\langle T_2,T_0\rangle,\qquad
T_3=\langle T_2,T_1\rangle,\qquad E_0[1,3]\ne T_3.
```

</td></tr></tbody></table>

两者数量分别为七和八。

证明。右子树分别为 $`\alpha`$ 和 $`\beta`$，自由树的叶标签不同，故来源不同。组成分别为 $`(2,1)^{\mathsf{\text{𝖳}}}`$ 和 $`(1,2)^{\mathsf{\text{𝖳}}}`$，施加 $`q`$ 给七、八。∎

**命题 2.4（集合顺序不供应来源顺序）。** 虽然 $`\{1,3\}=\{3,1\}`$，但

```math
\langle C_j,A_j\rangle\ne\langle A_j,C_j\rangle.
```

这两棵树组成相同，而选择项只有在连同定义 2.1 的编译约定保存时才指定本卷的代表。

证明。$`C_j`$ 的叶数严格大于 $`A_j`$，故两棵树左右子树不同；组成加法却交换，所以两者组成都为 $`c(C_j)+c(A_j)`$。无序位置集合没有额外的左右序字段。∎

作为来源次序的具名读出，二阶卷 §§101–103、106–107 另规定

```math
P_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
P_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
P_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad a=-iP_x,\quad b=-iP_y,\quad c_{\mathrm Q}=ba=iP_z,
```

```math
U_\alpha=a,\qquad U_\beta=b,\qquad
U_{\langle s,t\rangle}=U_sU_t.
```

在这一个表示内，$`ab=-c_{\mathrm Q}`$、$`ba=c_{\mathrm Q}`$，所以相同组成的两种叶序仍可保留相对负号；二阶卷定理 106.2 证明该负号在全部 $`\rho^n`$ 推进中持续。零层联合代表的读出为 $`c_{\mathrm Q}a=-b`$，交换代表则给 $`ac_{\mathrm Q}=b`$。这依赖本段明确矩阵和乘序，不成为“联合选择等于第二位置的负值”的普遍模式等式。矩阵 $`U_sU_t`$ 对态先作用右因子；来源书写顺序也不能直接当作实际执行时间顺序。单系统通道中整体负号消去；相干区分另外需要二阶卷定义 107.1 的同参照、相位确定的受控实现及控制测量。原生整数读者不因这份附加表示而获得这些操作权限。

## 三、选择合并与来源生成是两种组合

**定义 3.1（合法选择的部分合并）。** 在固定同一窗口 $`j`$ 中，若 $`I,J\in\mathcal{\text{𝒮}}`$ 满足

```math
I\cap J=\varnothing,\qquad I\cup J\in\mathcal{\text{𝒮}},
```

定义

<table><tbody><tr><td>

```math
\mathsf{\text{𝖥}}_j[I]\boxplus\mathsf{\text{𝖥}}_j[J]
=\mathsf{\text{𝖥}}_j[I\cup J].
```

</td></tr></tbody></table>

其余输入对不定义。空选择是该部分运算的单位；重复占同一位置和新增相邻占位均不在定义域。该运算描述位置联合，不是原始有序树配对。

**命题 3.2（合法联合与生成的区别）。** 对每个 $`j\ge0`$，

<table><tbody><tr><td>

```math
\mathsf{\text{𝖥}}_j[1]\boxplus\mathsf{\text{𝖥}}_j[3]
=\mathsf{\text{𝖥}}_j[1,3],
```

</td></tr></tbody></table>

而 $`\mathsf{\text{𝖥}}_j[1]\boxplus\mathsf{\text{𝖥}}_j[2]`$ 不定义。同时原始来源层有

<table><tbody><tr><td>

```math
C_j=\langle B_j,A_j\rangle,\qquad
c(C_j)=c(A_j)+c(B_j).
```

</td></tr></tbody></table>

证明。集合 $`\{1,3\}`$ 不含相邻位置，集合 $`\{1,2\}`$ 含相邻位置；分别代入部分合并定义即得。来源等式则来自生成递归，其组成等式由组成映射的加法规则给出。它没有进行同窗位置的占位测试。∎

因此数量读出确有

```math
\mathrm{val}(\mathsf{\text{𝖥}}_j[3])
=\mathrm{val}(\mathsf{\text{𝖥}}_j[1])
+\mathrm{val}(\mathsf{\text{𝖥}}_j[2]),
```

却不能据此写合法模式等式 $`\mathsf{\text{𝖥}}_j[3]=\mathsf{\text{𝖥}}_j[1,2]`$，因为右项不属于 $`\mathcal{\text{𝒮}}`$。用两个来源生成第三个来源，与在同一受限窗口内同时占用两个位置，是不同操作：

<table><tbody><tr><td>

```math
\text{生成等式不等于同时占位许可。}
```

</td></tr></tbody></table>

编译 $`E_j`$ 同样不是把交换的部分并集无条件送到任意有序配对的同态。例如 $`1\boxplus3=3\boxplus1`$，而定义 2.1 只选定 $`\langle C_j,A_j\rangle`$，不把它与交换后的来源认同。位置标签使这项被数值相等掩盖的区别持续可见。

## 四、递归改变尺度，五模式保持选择形状

**定义 4.1（两个时钟与尺度组成）。** 标准 Fibonacci 数为

```math
\mathrm{Fib}_0=0,\qquad \mathrm{Fib}_1=1,\qquad
\mathrm{Fib}_{n+2}=\mathrm{Fib}_{n+1}+\mathrm{Fib}_n.
```

原子替换时钟一次推进 $`\rho`$；窗口尺度时钟一次推进三次替换。关系卷定义 1.3、定理 1.4 给

```math
c(\rho t)=Mc(t),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
H=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
q=(2,3),
```

```math
M^2=M+I_2,
\qquad qc(T_n)=\mathrm{Fib}_{n+3}\quad(n\ge0).
```

组成式可对两叶及二叉节点作结构归纳；数量式以二、三为初值，用 $`M^2=M+I_2`$ 得 Fibonacci 递推。这是来源与数量的桥，未把来源商成交换的数。

**定理 4.2（同一模板的全尺度运输）。** 对每个 $`j\in\mathbb{\text{ℕ}}`$ 和 $`I\in\mathcal{\text{𝒮}}`$，实际组成及数量为

<table><tbody><tr><td>

```math
c_j(I):=\widehat c(\widehat E_j[I])=H^j d_I=M^{3j}d_I,
\qquad
\mathrm{val}(\mathsf{\text{𝖥}}_j[I])=qH^j d_I
=\sum_{i\in I}\mathrm{Fib}_{3j+i+2}.
```

</td></tr></tbody></table>

对于非空选择，还满足

<table><tbody><tr><td>

```math
\rho^3(E_j[I])=E_{j+1}[I].
```

</td></tr></tbody></table>

证明。$`\rho^3(T_n)=T_{n+3}`$，且替换保持有序配对，所以每个单选代表及联合代表都同时后移三步，所选集合不变。组成运输由 $`c\rho=Mc`$ 迭代而来；对空贡献另外用零向量，$`H^j0=0`$，没有对空符号施加原始树替换。各单选项的数量为 $`\mathrm{Fib}_{3j+i+2}`$，联合代表的组成相加给求和式。∎

**命题 4.3（前三窗口的五数量）。** 按空、第一、第二、第三、联合端点的次序，数量为

| $`j`$ | $`\varnothing`$ | $`1`$ | $`2`$ | $`3`$ | $`1,3`$ |
| --- | --- | --- | --- | --- | --- |
| $`0`$ | $`0`$ | $`2`$ | $`3`$ | $`5`$ | $`7`$ |
| $`1`$ | $`0`$ | $`8`$ | $`13`$ | $`21`$ | $`29`$ |
| $`2`$ | $`0`$ | $`34`$ | $`55`$ | $`89`$ | $`123`$ |

证明。逐行使用定理 4.2。第一、第二、第三单选分别取 $`\mathrm{Fib}_{3j+3},\mathrm{Fib}_{3j+4},\mathrm{Fib}_{3j+5}`$；末列是第一与第三之和，得到七、二十九、一百二十三。∎

同一个选择形状并非始终同一个数量。例如第一位置在 $`j=1`$ 的实际组成是 $`c(T_3)=(1,2)^{\mathsf{\text{𝖳}}}`$，固定基坐标却一直是 $`d_1=(1,0)^{\mathsf{\text{𝖳}}}`$。第五至九节的组成坐标 $`\xi,\eta`$ 及其矩都使用这个固定基架，或等价地使用已知窗口中的相对组成；若读的是实际叶数，则先按 $`H^j`$ 运输解释。

**命题 4.4（单替换越过窗口边界）。** 对所有 $`j\ge0`$，单次替换依次给

<table><tbody><tr><td>

```math
A_j\xrightarrow{\rho}B_j
\xrightarrow{\rho}C_j\xrightarrow{\rho}A_{j+1}.
```

</td></tr></tbody></table>

最后一项不是 $`A_j`$。

证明。前三来源的轨道索引依次为 $`3j,3j+1,3j+2`$，下一索引为 $`3j+3`$。由二阶卷命题 21.2 的叶数递推，除最初两棵单叶树外叶数严格增长，最初两树的标签又不同，所以轨道各项两两不同。特别 $`T_{3j+3}\ne T_{3j}`$。∎

忘掉尺度标签后可以得到三角色的循环观察；它不证明来源自身三周期。$`\det M=-1`$ 使 $`H^j`$ 可逆，这只给整数组成或实坐标的逆线性运输，不给全部原始树上的逆替换。

## 五、正方形选择关系与 FIB 生成关系

**定义 5.1（低—高—中的占位坐标）。** 对 $`I\in\mathcal{\text{𝒮}}`$，置

```math
x(I)=\mathbf{\text{𝟏}}_{\{1\in I\}},\qquad
y(I)=\mathbf{\text{𝟏}}_{\{3\in I\}},\qquad
z(I)=\mathbf{\text{𝟏}}_{\{2\in I\}}.
```

因此 $`x,z,y`$ 是低到高的印刷位串，而占位向量使用 $`(x,y,z)`$ 次序，满足

```math
x,y,z\in\{0,1\},\qquad xz=yz=0.
```

五个向量为

```math
\begin{aligned}
v_{\varnothing}&=(0,0,0),&v_1&=(1,0,0),&v_2&=(0,0,1),\\
v_3&=(0,1,0),&v_{13}&=(1,1,0).
\end{aligned}
```

四棱锥顶点是 $`\mathsf{\text{𝖥}}[2]`$，即旧标签 $`[3]`$；第三位置 $`\mathsf{\text{𝖥}}[3]`$ 在底面上。

**定理 5.2（选择层的四棱锥与坐标体积）。** 采用该占位基架的标准欧氏内积及坐标 Lebesgue 测度，

<table><tbody><tr><td>

```math
\mathcal{\text{𝒫}}=\mathrm{conv}\{v_{\varnothing},v_1,v_2,v_3,v_{13}\}
=\{(X,Y,Z):X,Y,Z\ge0, X+Z\le1, Y+Z\le1\}.
```

</td></tr></tbody></table>

高度 $`Z`$ 截面的面积及总体积为

<table><tbody><tr><td>

```math
A(Z)=(1-Z)^2\quad(0\le Z\le1),\qquad
\mathrm{Vol}(\mathcal{\text{𝒫}})=\int_0^1(1-Z)^2\,dZ=\frac13.
```

</td></tr></tbody></table>

证明。五个顶点都满足所列线性不等式，故凸包包含于不等式域。反向，固定 $`Z\lt1`$ 并令 $`r=1-Z`$，则 $`0\le X/r,Y/r\le1`$，且

```math
(X,Y,Z)=r(X/r,Y/r,0)+Z(0,0,1).
```

底面点属于单位正方形，故右边是底面与顶点的凸组合。当 $`Z=1`$ 时不等式强制 $`X=Y=0`$，也在凸包。截面两条边长均为 $`1-Z`$，积分得到体积。∎

这是关联卷及基础卷数学引文 3.2 的同一凸体；Stanley note 的三元素 fence 以 $`(X,Z,Y)`$ 重排坐标给同一 chain polytope。凸体、坐标尺子和模式概率律是不同输入。体积三分之一是这份坐标测度的数值，不由它推出物理长度、空间维数或五模式的实际概率。

**命题 5.3（两条不同的混合关系）。** 选择层的底面正方形满足

<table><tbody><tr><td>

```math
v_{\varnothing}+v_{13}=v_1+v_3.
```

</td></tr></tbody></table>

把位置贡献展开为固定基组成，定义

<table><tbody><tr><td>

```math
\xi=x+y,\qquad \eta=y+z,\qquad d_I=(\xi(I),\eta(I))^{\mathsf{\text{𝖳}}}.
```

</td></tr></tbody></table>

其五点为

```math
\begin{aligned}
d_{\varnothing}&=(0,0)^{\mathsf{\text{𝖳}}},&d_1&=(1,0)^{\mathsf{\text{𝖳}}},&d_2&=(0,1)^{\mathsf{\text{𝖳}}},\\
d_3&=(1,1)^{\mathsf{\text{𝖳}}},&d_{13}&=(2,1)^{\mathsf{\text{𝖳}}},
\end{aligned}
```

另满足生成组成关系

<table><tbody><tr><td>

```math
d_{\varnothing}+d_3=d_1+d_2.
```

</td></tr></tbody></table>

证明。第一式逐坐标相加；两条底面对角线的中点相同。第二式用 $`d_3=d_1+d_2`$，它来自 $`c(C_0)=c(B_0)+c(A_0)`$。第一式在占位三空间成立，第二式只在组成投影后成立，因为 $`v_{\varnothing}+v_3\ne v_1+v_2`$。∎

例如等权混合 $`(\delta_{\varnothing}+\delta_{13})/2`$ 与 $`(\delta_1+\delta_3)/2`$ 有相同平均占位；这里的加法是概率混合，不是树配对，也不是对两项模式执行 $`\boxplus`$。第一条关系记录两端怎样共同出现，第二条关系记录第三位置与前两个生成来源之间怎样分配。尺度 $`j`$ 的实际组成点为 $`H^jd_I`$，仍满足第二条关系；固定基公式并未声称它们仍是零层叶数。

## 六、金字塔到梯形，以及全部闭概率纤维

**定义 6.1（归一化律和两个投影）。** 固定同一窗口尺度及编译约定，五模式律一律按以下次序：

```math
p=(p_{\varnothing},p_1,p_2,p_3,p_{13})\in\Delta_4,
\qquad p_I\ge0,\quad \sum_{I\in\mathcal{\text{𝒮}}}p_I=1.
```

占位均值及固定基组成均值为

```math
\begin{aligned}
X&=\mathbb{\text{𝔼}}_p[x]=p_1+p_{13},&
Y&=\mathbb{\text{𝔼}}_p[y]=p_3+p_{13},&
Z&=\mathbb{\text{𝔼}}_p[z]=p_2,\\
U&=\mathbb{\text{𝔼}}_p[\xi]=X+Y,&
V&=\mathbb{\text{𝔼}}_p[\eta]=Y+Z.
\end{aligned}
```

于是映射为

```math
\Delta_4\xrightarrow{\pi_{\mathrm{occ}}}\mathcal{\text{𝒫}}
\xrightarrow{L}\mathcal{\text{𝒟}},
\qquad
L=\begin{pmatrix}1&1&0\\0&1&1\end{pmatrix},
\qquad L(X,Y,Z)^{\mathsf{\text{𝖳}}}=(U,V)^{\mathsf{\text{𝖳}}}.
```

实际尺度组成均值另外是 $`H^j(U,V)^{\mathsf{\text{𝖳}}}`$。

**定理 6.2（占位投影的全部纤维）。** 给 $`(X,Y,Z)\in\mathcal{\text{𝒫}}`$，令 $`r=1-Z`$。其全部相容律恰为

```math
\begin{aligned}
p_{\varnothing}&=r-X-Y+\kappa,\\
p_1&=X-\kappa,\qquad p_2=Z,\\
p_3&=Y-\kappa,\qquad p_{13}=\kappa,
\end{aligned}
```

<table><tbody><tr><td>

```math
\max(0,X+Y-r)\le\kappa\le\min(X,Y).
```

</td></tr></tbody></table>

这条纤维的长度为

```math
w_\kappa=\min\{X,Y,r-X,r-Y\}.
```

当且仅当点在四张三角侧面 $`X=0`$、$`Y=0`$、$`X+Z=1`$、$`Y+Z=1`$ 的并集上，纤维是单点；其余点的纤维是非退化线段，包括底面正方形的内部。

证明。以 $`p_{13}=\kappa`$ 反解三个均值及归一化，得到五式。五概率非负等价于所列闭区间；$`X,Y\le r`$ 保证区间非空。按 $`X\le Y`$ 或其反向，以及 $`X+Y\le r`$ 或其反向，分别相减上下端即得宽度式。宽度为零恰是所列四个坐标等式之一。$`r=0`$ 时只有顶点，唯一律为 $`p_2=1`$。∎

这里复用基础卷数学引文 4.2 的闭纤维，只按位置重标概率。归一化超平面内两同占位律的差恰沿

<table><tbody><tr><td>

```math
g_{\square}=(1,-1,0,-1,1).
```

</td></tr></tbody></table>

**定理 6.3（组成像是梯形）。** 全部固定基平均组成的像为

<table><tbody><tr><td>

```math
\mathcal{\text{𝒟}}=
\{(U,V):0\le V\le1,\quad 0\le U\le1+V\}.
```

</td></tr></tbody></table>

其极端顶点依次可写为 $`(0,0),(1,0),(2,1),(0,1)`$。选择 $`\mathsf{\text{𝖥}}[3]`$ 的组成 $`(1,1)`$ 在上边内部，不是额外极端顶点。尺度 $`j`$ 的实际平均组成像是 $`H^j\mathcal{\text{𝒟}}`$，与固定基梯形线性等价。

证明。$`V=p_2+p_3+p_{13}\le1`$，$`U,V\ge0`$，且

```math
U-V=p_1+p_{13}-p_2\le1.
```

这给全部必要约束。反向，当 $`0\le V\le1`$，取 $`r_0\in[0,1-V]`$、$`r_1\in[0,2V]`$ 使 $`U=r_0+r_1`$，则

```math
(U,V)=
(1-V-r_0)(0,0)+r_0(1,0)
+(V-r_1/2)(0,1)+(r_1/2)(2,1).
```

四系数非负且和一，所列顶点均为实际模式组成。所需拆分存在，因为两个区间之和为 $`[0,1+V]`$。点 $`(1,1)`$ 是上边两端的中点。∎

**定理 6.4（组成投影的全部纤维及维数下降）。** 对任意 $`(U,V)\in\mathcal{\text{𝒟}}`$，令 $`Y=y_0`$、$`p_{13}=\kappa`$。全部相容概率恰为

<table><tbody><tr><td>

```math
\begin{aligned}
p_{\varnothing}&=1-U-V+y_0+\kappa,\\
p_1&=U-y_0-\kappa,\\
p_2&=V-y_0,\\
p_3&=y_0-\kappa,\\
p_{13}&=\kappa,
\end{aligned}
```

</td></tr></tbody></table>

其完整合法范围为

<table><tbody><tr><td>

```math
\max\left(0,\frac{U+V-1}{2}\right)
\le y_0\le\min(U,V),
```

</td></tr></tbody></table>

<table><tbody><tr><td>

```math
\max(0,U+V-y_0-1)
\le\kappa\le\min(U-y_0,y_0).
```

</td></tr></tbody></table>

梯形内部的纤维为二维；上边 $`V=1,\ 0\lt U\lt2`$ 的纤维为一维；其余三条边以及四个顶点的纤维为单点。

证明。$`X=U-y_0`$、$`Z=V-y_0`$，代入定理 6.2 即得反解。非负性要求 $`y_0\le V`$，以及

```math
\kappa\ge0,\quad \kappa\ge U+V-y_0-1,\quad
\kappa\le U-y_0,\quad \kappa\le y_0.
```

上下端相容等价于 $`0\le y_0\le U`$、$`V\le1`$ 和 $`2y_0\ge U+V-1`$，给所列两个闭区间。反向在区间内代入，五项非负且和为一，故没有漏掉端点。

若 $`0\lt V\lt1`$ 且 $`0\lt U\lt1+V`$，第一段的下端严格小于上端；选其内点 $`y_0`$ 后，第二段也可取严格内点，使五概率都正。两参数的独立差因此给二维纤维。

上边 $`V=1`$ 强制 $`p_{\varnothing}=p_1=0`$，于是 $`\kappa=U-y_0`$，其范围化为

```math
U/2\le y_0\le\min(U,1).
```

对 $`0\lt U\lt2`$ 这是非退化线段，两个端点 $`U=0,2`$ 则唯一。其余边直接由非负概率给

| 边界 | $`(p_{\varnothing},p_1,p_2,p_3,p_{13})`$ |
| --- | --- |
| $`V=0`$ | $`(1-U,U,0,0,0)`$ |
| $`U=0`$ | $`(1-V,0,V,0,0)`$ |
| $`U=1+V`$ | $`(0,1-V,0,0,V)`$ |

故均为单点，四角也包含在这些公式内。∎

该闭纤维沿用双曲卷定理 7.5；本卷固定概率顺序后，两条独立不可见方向为

<table><tbody><tr><td>

```math
g_{\square}=(1,-1,0,-1,1),\qquad
g_{\mathrm{fib}}=(1,-1,-1,1,0).
```

</td></tr></tbody></table>

归一化、$`U`$、$`V`$ 的约束矩阵在空、第一、第二模式三列上已秩三，故其核恰为二维；上述两个向量独立，遂穷尽线性核。参数增量是 $`\delta y_0\,g_{\mathrm{fib}}+\delta\kappa\,g_{\square}`$，非负性再把它截成上述闭纤维。全维关系为

<table><tbody><tr><td>

```math
\text{完整概率体：四自由参数}
\longrightarrow\text{占位金字塔：三均值}
\longrightarrow\text{组成梯形：两均值}.
```

</td></tr></tbody></table>

它说明读出逐步合并来源分配，不意味着物理空间维数消失；“恰好两项关联参数”指完整仿射核和一般内部纤维，退化边界的实际自由度按本定理下降。

## 七、任意目标读出：组成与两种关系的分解

**定义 7.1（目标的两项关系系数）。** 对任意有限实函数 $`f:\mathcal{\text{𝒮}}\to\mathbb{\text{ℝ}}`$，将其五值按本卷顺序写为 $`f_{\varnothing},f_1,f_2,f_3,f_{13}`$，定义

<table><tbody><tr><td>

```math
\Gamma_f=f_{\varnothing}+f_3-f_1-f_2,\qquad
\Lambda_f=f_{\varnothing}+f_{13}-f_1-f_3.
```

</td></tr></tbody></table>

$`\Gamma_f`$ 检查目标是否区分生成组成关系的两侧，$`\Lambda_f`$ 检查它是否区分正方形两条对角线。函数指的是该五模式域上的读出；对完整回复分布，须分别使用每个回复事件的指示函数。

**定理 7.2（全部平均目标的精确展开）。** 对每个 $`p\in\Delta_4`$，

<table><tbody><tr><td>

```math
\begin{aligned}
\mathbb{\text{𝔼}}_p[f]
={}&f_{\varnothing}
+(f_1-f_{\varnothing})U
+(f_2-f_{\varnothing})V\\
&+\Gamma_fY+\Lambda_f\kappa,
\qquad \kappa=p_{13}.
\end{aligned}
```

</td></tr></tbody></table>

存在一个仅以 $`U,V`$ 为输入、对全部归一化五模式律正确的平均目标读出，当且仅当

<table><tbody><tr><td>

```math
\Gamma_f=\Lambda_f=0.
```

</td></tr></tbody></table>

证明。把定理 6.4 的五概率代入 $`\sum_Ip_If_I`$ 并逐项整理，得到展开式。若两系数为零，右边显然仅依赖 $`U,V`$。

必要性分别使用两对合法律：

```math
\frac12(\delta_{\varnothing}+\delta_3),\qquad
\frac12(\delta_1+\delta_2),
```

```math
\frac12(\delta_{\varnothing}+\delta_{13}),\qquad
\frac12(\delta_1+\delta_3).
```

第一对的组成均值均为 $`(1/2,1/2)`$，平均目标之差为 $`\Gamma_f/2`$；第二对的组成均值均为 $`(1,1/2)`$，差为 $`\Lambda_f/2`$。若目标对所有同组成均值的律都相同，两差必须为零。∎

这是基础卷 §七的目标差分接到双曲卷组成纤维后的分解。它让应保存的关系逐目标判断，而非只凭图形维数判断。按占位均值展开的同一等式为

```math
\mathbb{\text{𝔼}}_p[f]=f_{\varnothing}
+(f_1-f_{\varnothing})X
+(f_3-f_{\varnothing})Y
+(f_2-f_{\varnothing})Z+\Lambda_f\kappa.
```

故三占位均值对全体律足够的条件仅是 $`\Lambda_f=0`$；再压成组成均值时才增加 $`\Gamma_f=0`$。

**命题 7.3（全域条件与特定退化纤维）。** 对固定组成均值 $`(U,V)`$，平均目标可由该摘要唯一决定，恰当且仅当

```math
\Gamma_f(y_0'-y_0)+\Lambda_f(\kappa'-\kappa)=0
```

对定理 6.4 中全部合法参数对成立。内部纤维的条件是 $`\Gamma_f=\Lambda_f=0`$；开上边 $`V=1,0\lt U\lt2`$ 的条件是 $`\Gamma_f=\Lambda_f`$；其他边及顶点没有额外系数限制。

证明。同摘要两律的目标差正是所列线性式。内部纤维含两参数开集，故两个独立方向都须被消去。上边有 $`\kappa=U-y_0`$，差化为 $`(\Gamma_f-\Lambda_f)(y_0'-y_0)`$，非退化线段给所列条件。单点纤维没有非零差。∎

因此不能把“对全部律充分”的两个零系数要求当成每个退化边界的必要条件。对固定占位纤维也同样：宽度 $`w_\kappa=0`$ 时任何目标都已确定，宽度正时只需检查 $`\Lambda_f`$。来源分配是否重要，由实际纤维和实际目标共同决定。

## 八、二阶组成读数恢复全部五模式概率

**定义 8.1（同一模式上的二阶组成边界）。** 在固定基架上，除 $`U=\mathbb{\text{𝔼}}_p[\xi]`$、$`V=\mathbb{\text{𝔼}}_p[\eta]`$ 外，保留

<table><tbody><tr><td>

```math
S=\mathbb{\text{𝔼}}_p[\xi(\xi-1)],\qquad
T=\mathbb{\text{𝔼}}_p[\xi\eta].
```

</td></tr></tbody></table>

这里 $`S,T`$ 是矩的符号，$`T_n`$ 才是来源树；两乘积中的分量来自同一次模式实现。五个确定模式的完整评价为

| 模式 | $`(\xi,\eta)`$ | $`\xi(\xi-1)`$ | $`\xi\eta`$ |
| --- | --- | ---: | ---: |
| $`\mathsf{\text{𝖥}}[\varnothing]`$ | $`(0,0)`$ | $`0`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[1]`$ | $`(1,0)`$ | $`0`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[2]`$ | $`(0,1)`$ | $`0`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[3]`$ | $`(1,1)`$ | $`0`$ | $`1`$ |
| $`\mathsf{\text{𝖥}}[1,3]`$ | $`(2,1)`$ | $`2`$ | $`2`$ |

确定模式到组成点仍是单射；歧义发生在只取平均以后，不是该五点表已经合并模式。

**定理 8.2（四项读数的完整概率反演）。** 对任意归一化五模式律，

<table><tbody><tr><td>

```math
\begin{aligned}
p_{13}&=\frac S2,\\
p_3&=T-S,\\
p_2&=V-T+\frac S2,\\
p_1&=U-T,\\
p_{\varnothing}&=1-U-V+T.
\end{aligned}
```

</td></tr></tbody></table>

反向，实四元组 $`(U,V,S,T)`$ 来自合法五模式律，当且仅当

<table><tbody><tr><td>

```math
\begin{gathered}
S\ge0,\qquad T-S\ge0,\\
V-T+\frac S2\ge0,\qquad U-T\ge0,\\
1-U-V+T\ge0.
\end{gathered}
```

</td></tr></tbody></table>

这些约束包含全部退化边界；五个反解概率自动相加为一。

证明。由定义 8.1 的五点评价，

```math
S=2p_{13},\qquad T=p_3+2p_{13},\qquad
U=p_1+p_3+2p_{13},\qquad
V=p_2+p_3+p_{13}.
```

先解 $`p_{13}`$ 和 $`p_3`$，再解 $`p_2,p_1`$，最后用归一化给空模式概率，得到反演。必要性来自每项概率非负。充分性则把五式作为概率定义；所列不等式保证非负，相加给一，代回四矩式恢复原四元组。∎

**命题 8.3（已有五函数代数的基变换）。** 在当前合法域上逐点有

```math
\xi(\xi-1)=2xy,\qquad \xi\eta=y+xy,
\qquad
\kappa=S/2,\qquad Y=T-S/2.
```

因此 $`1,\xi,\eta,\xi(\xi-1),\xi\eta`$ 是全部五模式实函数的一组基；任意平均目标也可写为

<table><tbody><tr><td>

```math
\mathbb{\text{𝔼}}_p[f]=f_{\varnothing}
+(f_1-f_{\varnothing})U
+(f_2-f_{\varnothing})V
+\Gamma_fT+\frac{\Lambda_f-\Gamma_f}{2}S.
```

</td></tr></tbody></table>

证明。$`x^2=x,y^2=y,z^2=z,xz=yz=0`$，展开两个乘积即得点态恒等式。五函数按五模式评价的矩阵是

```math
\mathcal{\text{ℰ}}=
\begin{pmatrix}
1&0&0&0&0\\
1&1&0&0&0\\
1&0&1&0&0\\
1&1&1&0&1\\
1&2&1&2&2
\end{pmatrix},\qquad \det\mathcal{\text{ℰ}}=-2\ne0.
```

故评价基满秩。平均目标式也可直接把 $`Y=T-S/2,\kappa=S/2`$ 代入定理 7.2。∎

基础卷数学引文 2.2 已给出基 $`1,x,y,z,xy`$ 及完整事件代数；本节是它的明确坐标变换，不增加原子或不可见本体。$`\xi(\xi-1)`$ 在当前五模式域恰标记联合选择的两个第一类组成贡献；$`\xi\eta`$ 读两个分量怎样共同出现。一阶告诉各方向平均有多少，二阶补回共同出现关系。

**命题 8.4（平均乘积不能由均值乘积替代）。** 对一般合法律，不能把 $`S,T`$ 换成 $`U(U-1),UV`$。例如令

```math
\mu_A=\tfrac12\delta_{\varnothing}+\tfrac12\delta_{13},\qquad
\mu_B=\tfrac12\delta_1+\tfrac12\delta_3.
```

两律同有 $`U=1,V=1/2`$，但

```math
(S_A,T_A)=(1,1),\qquad (S_B,T_B)=(0,1/2).
```

证明。逐模式代入表；均值产品在两律上都是 $`UV=1/2`$，且 $`U(U-1)=0`$，无法给出第一律的真实二阶平均。一般也有

```math
S=U(U-1)+\mathrm{Var}_p(\xi),\qquad
T=UV+\mathrm{Cov}_p(\xi,\eta).
```

故被删除的方差与协方差正可承载关系。∎

**定义 8.5（生成多项式）。** 定义有限支撑的概率生成函数

<table><tbody><tr><td>

```math
\mathcal{\text{𝒢}}_p(s,t)=p_{\varnothing}+p_1s+p_2t+p_3st+p_{13}s^2t.
```

</td></tr></tbody></table>

这里 $`s,t`$ 是形式变量，不是第十节的接缝位。

**命题 8.6（二阶导数恢复全部系数）。** 有

<table><tbody><tr><td>

```math
\begin{aligned}
\mathcal{\text{𝒢}}_p(1,1)&=1,\\
\partial_s\mathcal{\text{𝒢}}_p(1,1)&=U,\\
\partial_t\mathcal{\text{𝒢}}_p(1,1)&=V,\\
\partial_s^2\mathcal{\text{𝒢}}_p(1,1)&=S,\\
\partial_s\partial_t\mathcal{\text{𝒢}}_p(1,1)&=T.
\end{aligned}
```

</td></tr></tbody></table>

证明。对五个单项式逐项求导，在 $`(1,1)`$ 评价，依次得到归一化、一阶指数、第二阶阶乘指数及共同指数。定理 8.2 遂恢复全部系数。这里只用有限多项式代数，没有无限级数交换问题。∎

**命题 8.7（已知尺度上的二阶运输）。** 令随机固定基组成 $`D=(\xi,\eta)^{\mathsf{\text{𝖳}}}`$，实际尺度组成为 $`D_j=H^jD`$。其一阶均值与原始二阶矩矩阵满足

```math
\bar D_j=H^j\begin{pmatrix}U\\V\end{pmatrix},\qquad
R=\mathbb{\text{𝔼}}_p[DD^{\mathsf{\text{𝖳}}}]
=\begin{pmatrix}U+S&T\\T&V\end{pmatrix},\qquad
R_j=H^jR(H^j)^{\mathsf{\text{𝖳}}}.
```

若已知尺度 $`j`$ 并取得这些实际一、二阶矩，则可先用

```math
\begin{pmatrix}U\\V\end{pmatrix}=H^{-j}\bar D_j,
\qquad R=H^{-j}R_j(H^{-j})^{\mathsf{\text{𝖳}}},
\qquad S=R_{11}-U,\quad T=R_{12}
```

回到固定基坐标，再使用定理 8.2。

证明。$`\xi^2=\xi+\xi(\xi-1)`$，而五点中 $`\eta\in\{0,1\}`$，所以 $`\eta^2=\eta`$，得 $`R`$。确定线性映射与有限期望交换，给均值及矩阵运输。$`\det H=-1`$，故逆存在并给反解。∎

不能把实际高层两分量直接代入零层五点反演；逆坐标运输也不授予逆树操作。窗口尺度、测得的分量及使用的矩必须一起声明。

**命题 8.8（精确数量记录与概率取得的区别）。** 在原生初态一次零层读窗的合同内，首次精确数量 $`Q\in\{0,2,3,5,7\}`$ 对该次模式单射，并逐样本给

```math
\begin{aligned}
\xi&=\mathbf{\text{𝟏}}_{\{Q=2\}}+\mathbf{\text{𝟏}}_{\{Q=5\}}+2\mathbf{\text{𝟏}}_{\{Q=7\}},\\
\eta&=\mathbf{\text{𝟏}}_{\{Q\text{ 为奇数}\}},\\
\xi(\xi-1)&=2\mathbf{\text{𝟏}}_{\{Q=7\}},\\
\xi\eta&=\mathbf{\text{𝟏}}_{\{Q=5\}}+2\mathbf{\text{𝟏}}_{\{Q=7\}}.
\end{aligned}
```

因此一份已保留的同样本精确数量记录供应这些特征；有限记录的平均给其经验矩，定理 8.2 恰恢复该记录的经验律。单个模式、单个数量或一份有限记录不自动确定未知总体律。

证明。五个不同数量分别指认表中五行，所以每个特征式逐行成立。对同一有限记录求平均，线性反演与平均交换，恢复各模式出现频率。若总体律未知，不同严格正律都可给同一个被观察模式正概率，且都可产生同一有限记录，故该记录不能唯一确定真律。∎

给定精确总体矩时的代数恢复、已取得记录的经验恢复、对未知总体的统计估计是三个不同结论。估计所需的重复取得、独立同律或其他实际抽样合同必须另外成立；本节不预设来源复制、重置或免费精确期望读口，也不把两份不同样本的分量乘积当成同窗乘积。

## 九、无限 FIB 均值读取仍只保留两个组成均值

**定义 9.1（同一律的尺度响应）。** 对固定同一 $`p\in\Delta_4`$，定义

```math
m_n(p)=\mathbb{\text{𝔼}}_p[qM^nD]
=qM^n\begin{pmatrix}U\\V\end{pmatrix}\qquad(n\ge0).
```

这是同一来源在组成表示中的原子尺度响应，不声明每个响应均已通过实际操作取得；如果每次变换来源律，便不是本定义。

**定理 9.2（整条均值序列的精确信息）。** 对任意两份合法律 $`p,p'`$，

<table><tbody><tr><td>

```math
(m_n(p))_{n\ge0}=(m_n(p'))_{n\ge0}
\iff (U(p),V(p))=(U(p'),V(p')).
```

</td></tr></tbody></table>

其中

```math
m_0=2U+3V,\qquad m_1=3U+5V,
```

<table><tbody><tr><td>

```math
U=5m_0-3m_1,\qquad V=-3m_0+2m_1,
```

</td></tr></tbody></table>

```math
m_{n+2}=m_{n+1}+m_n.
```

证明。两初值的矩阵为

```math
\begin{pmatrix}m_0\\m_1\end{pmatrix}
=\begin{pmatrix}2&3\\3&5\end{pmatrix}
\begin{pmatrix}U\\V\end{pmatrix},\qquad
\begin{pmatrix}2&3\\3&5\end{pmatrix}^{-1}
=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
```

行列式一，故序列相等蕴涵两个组成均值相等；反向直接由定义。$`M^2=M+I_2`$ 给递推，因此后续均值没有新独立参数。也可写

```math
m_n=\mathrm{Fib}_{n+3}U+\mathrm{Fib}_{n+4}V.
```

∎

这是双曲卷定理 7.3 在整数替换时钟上的同源结论。它的两参数纤维正是定理 6.4；任意多次读取这类均值都不能分开两条不可见方向。采样更多与读取更丰富的关系不同：增加同一均值的精度，不产生 $`S,T`$。

**命题 9.3（连续线性表示也不补回二阶矩）。** 沿用双曲卷的固定复分支，令

```math
\phi=\frac{1+\sqrt5}{2},\qquad \psi=\frac{1-\sqrt5}{2},\qquad
P_+=\frac{M-\psi I_2}{\phi-\psi},\qquad
P_-=\frac{\phi I_2-M}{\phi-\psi},
```

```math
\mathcal{\text{𝒰}}(t)=\phi^tP_++e^{-i\pi t}|\psi|^tP_-
\quad(t\in\mathbb{\text{ℝ}}),\qquad
\bar f_p(t)=\mathbb{\text{𝔼}}_p[q\mathcal{\text{𝒰}}(t)D].
```

整条 $`\bar f_p`$ 只依赖 $`U,V`$，且整条曲线相等仍当且仅当两个组成均值相等。

证明。有限期望与固定线性映射交换，得 $`\bar f_p(t)=q\mathcal{\text{𝒰}}(t)(U,V)^{\mathsf{\text{𝖳}}}`$；整数 $`n`$ 时 $`\mathcal{\text{𝒰}}(n)=M^n`$，曲线包含定理 9.2 的前两读数，故反向也成立。∎

这只指声明的完整分支和完整曲线；只保留某时刻的实投影还可丢失更多信息，双曲卷定理 7.3–7.4 已给具体范围。非整数表示时间不是原生读者的新动作。第二阶、乘积、次序或联合事件读口可补回它们实际读取的关系，反复读取一种一阶响应则不能。第十一节改用确实声明的原生数量动作来构成取得桥，不把连续表示当作免费仪器。

## 十、递归接缝：五模式与一个合法性边界位

**定义 10.1（原生高到低守卫）。** 本节固定关系卷定义 7.1 的 HIGH-to-LOW 读向：窗口从高向低输入，窗口内部三位仍按低、中、高印刷。定义

```math
\ell(I)=\mathbf{\text{𝟏}}_{\{1\in I\}}=x(I),\qquad
h(I)=\mathbf{\text{𝟏}}_{\{3\in I\}}=y(I).
```

旧接缝 $`s\in\{0,1\}`$ 是此前较高窗口的最低位是否占用。当前输入合法当且仅当

<table><tbody><tr><td>

```math
s\,h(I)=0,\qquad \text{合法后 }s'=\ell(I).
```

</td></tr></tbody></table>

非法输入进入独立吸收结果 $`\bot`$。五模式表为

| 输入模式 | 印刷三位：低、中、高 | 允许的旧接缝 | 新接缝 |
| --- | --- | --- | ---: |
| $`\mathsf{\text{𝖥}}[\varnothing]`$ | $`000`$ | $`0,1`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[1]`$ | $`100`$ | $`0,1`$ | $`1`$ |
| $`\mathsf{\text{𝖥}}[2]`$ | $`010`$ | $`0,1`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[3]`$ | $`001`$ | $`0`$ | $`0`$ |
| $`\mathsf{\text{𝖥}}[1,3]`$ | $`101`$ | $`0`$ | $`1`$ |

**定理 10.2（两个活接缝状态的充分性与可区分性）。** 对上述合法性任务，任意合法前缀的全部后缀许可只依赖它的接缝位。两个活状态 $`s=0,1`$ 不能再合并；独立错误结果另行保留。

证明。窗口内已按 $`\mathcal{\text{𝒮}}`$ 检查；唯一跨界相邻对是旧最低位和新最高位，故下一步许可只需 $`s`$。合法后新最低位成为唯一新接缝，归纳覆盖任意有限后缀。两活状态都可从初始零接缝达到：空窗留下零，第一位置留下一个一。后缀 $`\mathsf{\text{𝖥}}[3]`$ 在零状态合法，在一状态非法，所以它们的后缀语言不同。∎

五种模式、三维占位均值和一个接缝位回答不同问题。定理 10.2 只最小化合法后缀语言的活边界；数量预测还要保留组成状态，随机来源的未来分布还要保留实际联合或条件律。它不声称任意历史只需一个位，也不把吸收错误隐藏进合法零状态。

**定义 10.3（位置活动权及单位置核）。** 给位置一、二、三分别活动权 $`a,b,c`$，五模式的权为

```math
w_{\varnothing}=1,\quad w_1=a,\quad w_2=b,\quad
w_3=c,\quad w_{13}=ac.
```

活动权只属于本节，不与第二节的 Pauli 原语混用。单位置核的行是旧占位、列是新占位，均按零、一排序：

```math
B(t)=\begin{pmatrix}1&t\\1&0\end{pmatrix}.
```

新位为零权一，旧零新一权 $`t`$，相邻两个一权零。

**命题 10.4（双扫描核与环内行列式）。** 在交换半环上的活动权恒等式为

<table><tbody><tr><td>

```math
K_{\mathrm{HL}}(a,b,c)
=B(c)B(b)B(a)
=\begin{pmatrix}
1+b+c&a(1+c)\\
1+b&a
\end{pmatrix}.
```

</td></tr></tbody></table>

辅助低到高扫描是另一个接口：

```math
K_{\mathrm{LH}}(a,b,c)
=B(a)B(b)B(c)
=\begin{pmatrix}
1+a+b&c(1+a)\\
1+b&c
\end{pmatrix}.
```

如果系数载体是交换环，才另外有

<table><tbody><tr><td>

```math
\det K_{\mathrm{HL}}=\det K_{\mathrm{LH}}=-abc.
```

</td></tr></tbody></table>

证明。高到低实际位置顺序为三、二、一，连续转移按行向量从左向右乘 $`B(c),B(b),B(a)`$，中间指标是同一个真实位。直接相乘给矩阵。也可从模式表枚举：输入零输出零有空、第二、第三项，权和 $`1+b+c`$；输入零输出一有第一和端点联合，权和 $`a+ac`$；输入一输出零只余空与第二项，输出一只余第一项，给第二行。辅助低到高则交换输入和输出所贴的端点角色，逐位乘法给另一式。交换环中 $`\det B(t)=-t`$，或者直接展开两个二阶行列式，都给 $`-abc`$。∎

这是关联卷推导 8.3 和基础卷数学引文 11.2 的有向核。半环中可求和与相乘，不自动有减法或行列式；环内允许负权或复权时，它仍是代数恒等式，不能自动作概率解释。辅助扫描与原生扫描在全一权时碰巧同矩阵，不因此成为相同的在线操作。反转完整词还须反转窗口次序并对应外端条件，原生前缀数量回复也须另核对。

**定义 10.5（同源路径权与端点）。** 对 $`L\ge0`$ 个从高到低输入的窗口 $`I_1,\ldots,I_L`$，声明路径权为

```math
W=\lambda(s_0)\mu(s_L)
\prod_{k=1}^L
a_k^{x(I_k)}b_k^{z(I_k)}c_k^{y(I_k)}
\prod_{k=1}^L\mathbf{\text{𝟏}}_{\{s_{k-1}h(I_k)=0\}},
\qquad s_k=\ell(I_k).
```

外端权为列向量 $`\lambda,\mu`$；空积为一。定义中的实际联合权因子化是前提，不由各窗边缘概率自动推出。

**命题 10.6（动态规划的合法域）。** 全路径权之和为

```math
\mathscr{\text{𝒵}}=\lambda^{\mathsf{\text{𝖳}}}
K_{\mathrm{HL},1}\cdots K_{\mathrm{HL},L}\mu.
```

对非负实权且 $`\mathscr{\text{𝒵}}\gt0`$，$`W/\mathscr{\text{𝒵}}`$ 才给这份已声明路径族的概率律。

证明。每条实际合法词唯一确定所有中间接缝；相邻核的输出和输入使用同一个位，局部模式唯一拼成该词。有限分配律把矩阵积展开为恰好这些路径权，不漏项、不交叉拼入不可能的联合实现。非负性及正总权给归一化概率。∎

本式沿用关联卷推导 8.4 的实际切口和权重合同。它并不要求枚举计数中的窗口“随机独立”；但用局部边缘矩阵去预测任意相关长历史，需要那份历史确实满足所声明的因子化或足够的条件核。

**定理 10.7（开放端合法词数）。** 位置权全一，高端外接缝固定零、低端输出自由，单位位固定零，允许高端空窗填充，包括空词，并无最高窗口非空或额外停止动作要求。令

```math
A=\begin{pmatrix}3&2\\2&1\end{pmatrix},\qquad
a_L=(1,0)A^L\begin{pmatrix}1\\1\end{pmatrix}.
```

则对每个 $`L\ge0`$，

<table><tbody><tr><td>

```math
a_L=\mathrm{Fib}_{3L+2},\qquad
a_{L+2}=4a_{L+1}+a_L,\qquad a_0=1,\quad a_1=5.
```

</td></tr></tbody></table>

证明。$`B(1)`$ 枚举一个位的无相邻一守卫，$`A=B(1)^3`$ 枚举一个三位窗口。长度 $`n`$、初接缝零、末端自由的二进制位词数 $`b_n`$ 有 $`b_0=1,b_1=2`$；从首位零或一分支得 $`b_{n+2}=b_{n+1}+b_n`$，故 $`b_n=\mathrm{Fib}_{n+2}`$。取 $`n=3L`$ 即第一式。直接相乘得到

```math
A^2=4A+I_2,
```

左右乘端点向量得到窗口时钟递推。∎

于是计数从 $`L=0`$ 起为 $`1,5,21,89,\ldots`$。两窗的二十五个形式标签对中，旧最低位一的第一或联合模式，与新最高位一的第三或联合模式形成四个冲突对，故只剩二十一。递归体由共享接缝筛选，不是 $`5^L`$ 个任意组合。固定末接缝、改变初接缝、计规范最高非空表示或闭环，都会改变端点合同，不能沿用这份计数。

**命题 10.8（概率核须保留拒绝质量）。** 若将同一提议律 $`p`$ 用于指定输入接缝，其合法输出的绝对质量核为

```math
K_{\mathrm{HL},p}=
\begin{pmatrix}
p_{\varnothing}+p_2+p_3&p_1+p_{13}\\
p_{\varnothing}+p_2&p_1
\end{pmatrix}
=\begin{pmatrix}
1-X&X\\
1-X-Y+\kappa&X-\kappa
\end{pmatrix}.
```

行和为 $`1,1-Y`$，其余拒绝质量分别为零、$`Y`$。若实际输入接缝与提议窗口相关，正概率接缝事件下应改用真实 $`p(I\mid s)`$，而非无条件律。

证明。逐接缝枚举定义 10.1 的合法模式即得矩阵和行和。输入一时被拒的是第三与联合模式，总质量 $`p_3+p_{13}=Y`$。对相关来源使用条件概率是同一枚举在该条件事件中的版本，零概率输入事件则没有条件律。∎

只有在通过质量正时才能条件化到“给定合法通过”；这改变了任务。把第二行独自归一化而丢弃拒绝，不保留一般整链的绝对概率。一个局部矩阵或接缝位也不会补回未给出的跨窗联合来源。

## 十一、遗漏关系在原生下一步出现，二阶边界怎样被任务消费

**定义 11.1（实际高到低数量读者）。** 直接使用关系卷定义 7.1 的整数读者。状态载体为

```math
\mathcal{\text{𝒳}}=(\{0,1\}\times\mathbb{\text{ℕ}}^2)\sqcup\{\bot\},
\qquad (s,C)_{\mathrm{init}}=(0,0).
```

在活态输入 $`I\in\mathcal{\text{𝒮}}`$，若 $`s\,h(I)=0`$，则

<table><tbody><tr><td>

```math
C'=HC+d_I,\qquad s'=\ell(I),\qquad Q'=qC'.
```

</td></tr></tbody></table>

否则进入吸收态 $`\bot`$；该态继续输入仍回复 $`\bot`$，与合法数量零不同。所有有限合法前缀即时回复，允许高端空填充，单位位为零，没有额外 End 动作。局部编译贡献始终是固定基 $`d_I`$；旧组成乘 $`H`$ 负责 Horner 尺度运输。按关系卷定理 7.2，低到高固定位置词 $`I_0,\ldots,I_{L-1}`$ 的逆序原生输入给

```math
C_{\mathrm{final}}=\sum_{j=0}^{L-1}H^jd_{I_j},\qquad
qC_{\mathrm{final}}=\sum_{j=0}^{L-1}\mathrm{val}(\mathsf{\text{𝖥}}_j[I_j]).
```

因此一个高到低输入尚未完成时的即时数量，不是预先固定最终高度后各窗口的绝对位置读数。实际空窗口执行 $`C'=HC,s'=0`$，既推进数量尺度又清零接缝，不是恒等或停止。

**命题 11.2（立即继续第三位置的实际表）。** 从初态输入一个 $`I\sim p`$ 后，在同一状态立即输入固定 $`\mathsf{\text{𝖥}}[3]`$，即旧标签 $`[5]`$，得到下表。其中 $`A_{\mathrm{odd}}`$ 是首次精确数量为奇数的事件。

| 首次模式 | 首次数量 $`Q`$ | $`\mathbf{\text{𝟏}}_{A_{\mathrm{odd}}}`$ | 首次后接缝 | 立即继续 $`\mathsf{\text{𝖥}}[3]`$ 的回复 $`R`$ |
| --- | ---: | ---: | ---: | --- |
| $`\mathsf{\text{𝖥}}[\varnothing]`$ | $`0`$ | $`0`$ | $`0`$ | $`5`$ |
| $`\mathsf{\text{𝖥}}[1]`$ | $`2`$ | $`0`$ | $`1`$ | $`\bot`$ |
| $`\mathsf{\text{𝖥}}[2]`$ | $`3`$ | $`1`$ | $`0`$ | $`18`$ |
| $`\mathsf{\text{𝖥}}[3]`$ | $`5`$ | $`1`$ | $`0`$ | $`26`$ |
| $`\mathsf{\text{𝖥}}[1,3]`$ | $`7`$ | $`1`$ | $`1`$ | $`\bot`$ |

证明。首次输入全部合法，留下 $`C=d_I,s=\ell(I)`$。下一固定输入的最高位是一，第一与联合模式留下的一接缝使其拒绝。三条合法分支分别给

```math
\begin{aligned}
q(Hd_{\varnothing}+d_3)&=5,\\
q(Hd_2+d_3)&=13+5=18,\\
q(Hd_3+d_3)&=21+5=26.
\end{aligned}
```

其余列直接由首次数量表和接缝定义。∎

本表是行列式卷命题 10.5、基础卷数学引文 11.7、双曲卷定理 7.8 的同一个原生继续任务，仅改为位置标签。每条分支属于同一初始化合同，没有另供复制、重置或反事实全表的实际取得。

**命题 11.3（金字塔均值不决定该完整回复律）。** 两份合法来源

```math
\mu_A=\frac12\delta_{\varnothing}+\frac12\delta_{13},\qquad
\mu_B=\frac12\delta_1+\frac12\delta_3
```

同有

```math
(X,Y,Z)=(1/2,1/2,0),\qquad (U,V)=(1,1/2),
```

故全部同源组成尺度均值也相同，然而立即继续回复律为

<table><tbody><tr><td>

```math
\nu_A=\frac12\delta_5+\frac12\delta_{\bot},\qquad
\nu_B=\frac12\delta_{\bot}+\frac12\delta_{26}.
```

</td></tr></tbody></table>

因此不存在仅从金字塔三均值正确给出该完整原生回复分布的规则。

证明。两律的平均占位相等来自正方形关系；组成均值及全部 $`m_n`$ 相等来自定理 9.2。按命题 11.2 推前，两律分别得到所列不同分布。假如回复分布经三均值下降，同一个输入摘要必给同一个分布，与两表相反。∎

该证明比较的是分布任务。两律的无条件拒绝概率都为二分之一，故单独拒绝率在这对律上没有差；不能把完整回复不足夸大为每个事件都不足。一次回复也不能精确识别未知总体律。

**定理 11.4（四矩恢复后的完整原生消费者）。** 给同一初始化来源律的精确固定基矩 $`U,V,S,T`$，命题 11.2 的回复律按 $`(5,18,26,\bot)`$ 次序恰为

<table><tbody><tr><td>

```math
\begin{aligned}
\nu_p(5)&=1-U-V+T,\\
\nu_p(18)&=V-T+\frac S2,\\
\nu_p(26)&=T-S,\\
\nu_p(\bot)&=U-T+\frac S2.
\end{aligned}
```

</td></tr></tbody></table>

它非负且总和一；在整个合法矩域包括退化边界都成立。

证明。定理 8.2 先恢复同一 $`p`$；按实际表，回复五、十八、二十六的质量分别为 $`p_{\varnothing},p_2,p_3`$，拒绝质量为 $`p_1+p_{13}`$。代入反解即得四式。前三项是概率，末项是两个概率之和，故非负；表穷尽所有首次模式，总质量一。∎

这是一项二阶恢复的实际任务消费：不仅给出新的坐标名称，也把恢复结果接到原有动作和独立拒绝结果。回复律单独仍可合并第一与联合模式；本定理没有声称该单次回复读口对五模式律单射。

**定理 11.5（实际奇偶记录下的条件回复与联合事件）。** 在命题 11.2 的同一历史中保留 $`A_{\mathrm{odd}}=\{Q\text{ 为奇数}\}`$，则

<table><tbody><tr><td>

```math
P_p(A_{\mathrm{odd}})=V,\qquad
P_p(A_{\mathrm{odd}},R=\bot)=\frac S2.
```

</td></tr></tbody></table>

当且仅当 $`V\gt0`$ 才定义该事件的条件回复律，其非零候选回复为

<table><tbody><tr><td>

```math
\begin{aligned}
P_p(R=18\mid A_{\mathrm{odd}})&=\frac{V-T+S/2}{V},\\
P_p(R=26\mid A_{\mathrm{odd}})&=\frac{T-S}{V},\\
P_p(R=\bot\mid A_{\mathrm{odd}})&=\frac{S}{2V}.
\end{aligned}
```

</td></tr></tbody></table>

证明。奇数记录只在第二、第三和联合模式上出现，概率为 $`p_2+p_3+p_{13}=V`$。记录为奇数且下一步拒绝只发生于联合模式，所以其事件指示函数逐点为 $`xy`$，概率为 $`p_{13}=S/2`$。条件事件质量正时将三支绝对质量除以 $`V`$；其和是 $`V`$，因此条件律归一化。$`V=0`$ 时事件不发生，不补出条件分布。∎

上面的两份正方形混合都有 $`V=1/2`$，但条件拒绝率分别为一和零。因此实际奇偶档案使遗漏的端点联合关系进入下一步任务，而无条件拒绝率仍为 $`X=U-T+S/2`$。若只保留真实联合档案 $`(A_{\mathrm{odd}},R)`$，五个模式对应的档案对是

```math
(0,5),\quad(0,\bot),\quad(1,18),\quad(1,26),\quad(1,\bot),
```

仍彼此不同，并给出同一总体律上的取得恒等式

```math
S=2P_p(A_{\mathrm{odd}},R=\bot),\qquad
T=P_p(R=26)+2P_p(A_{\mathrm{odd}},R=\bot).
```

精确档案律可用这些式子供矩；有限档案给对应经验矩。它们不表示各反事实动作已经全部执行，也不意味着把一个样本变成精确未知律。

**定义 11.6（另一条实际同执行取得路径）。** 从相同初态实际首读 $`I\sim p`$，记录数量 $`Q^{(0)}`$；随后在该同一状态实际输入空窗 $`\mathsf{\text{𝖥}}[\varnothing]`$，记录数量 $`Q^{(3)}`$。上标三表示经过三个组成替换，不是第三位置或第三个观测。若再输入第三位置，记最终回复为 $`R_{\mathrm{empty},3}`$。此路径的动作词为

```math
I,\quad\varnothing,\quad3.
```

空窗对两种接缝都合法，并清零接缝；后续第三位置因此也总合法。这条路径不同于立即继续第三位置的拒绝任务，不能相互替换。

**定理 11.7（两次数量的一、二阶统计取得矩边界）。** 对定义 11.6 的同一执行来源，逐样本有

```math
Q^{(0)}=2\xi+3\eta,\qquad Q^{(3)}=8\xi+13\eta.
```

令

```math
\mathfrak{\text{𝔞}}=\mathbb{\text{𝔼}}_p[Q^{(0)}],\qquad
\mathfrak{\text{𝔟}}=\mathbb{\text{𝔼}}_p[Q^{(3)}],
```

则

<table><tbody><tr><td>

```math
U=\frac{13\mathfrak{\text{𝔞}}-3\mathfrak{\text{𝔟}}}{2},\qquad
V=\mathfrak{\text{𝔟}}-4\mathfrak{\text{𝔞}}.
```

</td></tr></tbody></table>

再令

```math
h_0=\mathbb{\text{𝔼}}_p[(Q^{(0)})^2]-4U-9V,\qquad
h_3=\mathbb{\text{𝔼}}_p[(Q^{(3)})^2]-64U-169V,
```

便有

<table><tbody><tr><td>

```math
S=\frac{13h_0}{4}-\frac{3h_3}{16},\qquad
T=-h_0+\frac{h_3}{16}.
```

</td></tr></tbody></table>

证明。首读组成为 $`D=d_I`$，实际空窗后为 $`HD`$，且 $`qH=(8,13)`$，给点态两数量式。均值矩阵

```math
\begin{pmatrix}\mathfrak{\text{𝔞}}\\\mathfrak{\text{𝔟}}\end{pmatrix}
=\begin{pmatrix}2&3\\8&13\end{pmatrix}
\begin{pmatrix}U\\V\end{pmatrix}
```

的行列式为二，反解得到第一组公式。展开同样本平方，并用 $`\mathbb{\text{𝔼}}[\xi^2]=U+S,\mathbb{\text{𝔼}}[\eta^2]=V`$，得到

```math
\begin{aligned}
\mathbb{\text{𝔼}}_p[(Q^{(0)})^2]&=4U+9V+4S+12T,\\
\mathbb{\text{𝔼}}_p[(Q^{(3)})^2]&=64U+169V+64S+208T,
\end{aligned}
```

```math
\begin{pmatrix}h_0\\h_3\end{pmatrix}
=\begin{pmatrix}4&12\\64&208\end{pmatrix}
\begin{pmatrix}S\\T\end{pmatrix},\qquad
\det\begin{pmatrix}4&12\\64&208\end{pmatrix}=64.
```

反解恰为第二组公式。∎

该桥只用原生首读和原生空窗运输。两数量属于同一次执行、同一初始模式；没有把空窗当作来源重抽样，没有复制或重置。精确总体的一、二阶统计是定理的数学输入；对一份同执行配对记录逐式取平均，只恢复该记录的经验矩。若只观察两个数量均值而没有平方均值，则仍只取得 $`U,V`$，不能使用第二组公式。

**定理 11.8（空窗路径上的完整回复消费者）。** 在定义 11.6 中，最终第三位置回复为

```math
R_{\mathrm{empty},3}=q(H^2d_I+d_3).
```

其五个分支及质量为

| 首次模式 | $`Q^{(0)}`$ | 空窗后 $`Q^{(3)}`$ | 最终 $`R_{\mathrm{empty},3}`$ | 回复质量 |
| --- | ---: | ---: | ---: | --- |
| $`\mathsf{\text{𝖥}}[\varnothing]`$ | $`0`$ | $`0`$ | $`5`$ | $`1-U-V+T`$ |
| $`\mathsf{\text{𝖥}}[1]`$ | $`2`$ | $`8`$ | $`39`$ | $`U-T`$ |
| $`\mathsf{\text{𝖥}}[2]`$ | $`3`$ | $`13`$ | $`60`$ | $`V-T+S/2`$ |
| $`\mathsf{\text{𝖥}}[3]`$ | $`5`$ | $`21`$ | $`94`$ | $`T-S`$ |
| $`\mathsf{\text{𝖥}}[1,3]`$ | $`7`$ | $`29`$ | $`128`$ | $`S/2`$ |

定义 11.6 的精确数量统计，经定理 11.7 和 8.2，因而唯一给出该路径的完整回复律。

证明。实际空窗将接缝置零并把组成变成 $`Hd_I`$，第三位置遂合法，更新为 $`H^2d_I+d_3`$。$`qH^2=(34,55)`$ 且 $`qd_3=5`$，代入五个 $`d_I`$ 得五个互异回复。每个回复对应恰一首次模式，其质量是定理 8.2 的该概率。∎

**命题 11.9（均值全部相同而该路径的回复律不同）。** 命题 11.3 的两律在定义 11.6 下分别给

```math
\nu_{A,\mathrm{empty},3}=\tfrac12\delta_5+\tfrac12\delta_{128},\qquad
\nu_{B,\mathrm{empty},3}=\tfrac12\delta_{39}+\tfrac12\delta_{94}.
```

两律的所有一阶尺度均值相同，二阶数量统计及完整回复分布却不同。

证明。按定理 11.8 推前即可；第八节已给两律不同的 $`S,T`$。例如其数量平方均值分别为

```math
\begin{aligned}
\mathbb{\text{𝔼}}_{\mu_A}[(Q^{(0)})^2]&=49/2,&
\mathbb{\text{𝔼}}_{\mu_B}[(Q^{(0)})^2]&=29/2,\\
\mathbb{\text{𝔼}}_{\mu_A}[(Q^{(3)})^2]&=841/2,&
\mathbb{\text{𝔼}}_{\mu_B}[(Q^{(3)})^2]&=505/2.
\end{aligned}
```

所有一阶相等则由共同 $`U=1,V=1/2`$ 和定理 9.2。∎

立即第三位置任务包含拒绝，空窗后第三位置任务全部合法；两任务都使用同一个原生读者，但动作历史不同。新路径不能被用来删去原任务的拒绝分支。若首次数量 $`0,2,3,5,7`$ 已取得并精确保留，它已经识别该次模式；先把记录压成均值所造成的歧义，不能反说成原始来源不可知。完整未知概率律的取得仍受命题 8.8 的抽样边界限制。

## 十二、统一结构：每条箭头的来源、域与任务

**定义 12.1（选择到来源的有域关系链）。** 固定定义 2.1 的编译约定，并把窗口族记为 $`\mathcal{\text{𝒲}}_j=(A_j,B_j,C_j)`$。输入先给定尺度和选择，编译才给出所选来源。

从完整轨道到指定窗口的映射另定义为

```math
\mathrm{win}_j((T_n)_{n\ge0})=(T_{3j},T_{3j+1},T_{3j+2})=\mathcal{\text{𝒲}}_j.
```

选择项的编译链为

<table><tbody><tr><td>

```math
(j,I,\text{高位置在左的约定})
\xrightarrow{\sigma_j}\mathsf{\text{𝖥}}_j[I]
\xrightarrow{\widehat E_j}\mathbb{\text{𝕋}}_{\varnothing}.
```

</td></tr></tbody></table>

这里 $`\sigma_j`$ 的完整标签为“位置选择标签”；该标签箭头只是把 $`(j,I)`$ 记为选择项；编译箭头的输入域是 $`I\in\mathcal{\text{𝒮}}`$ 和已给窗口族，不是任意树。该选择项另有占位及组成读出：

```math
\mathcal{\text{𝒮}}\xrightarrow{v}\{v_I:I\in\mathcal{\text{𝒮}}\}\subset\mathbb{\text{ℝ}}^3
\xrightarrow{L}\{d_I:I\in\mathcal{\text{𝒮}}\}\subset\mathbb{\text{ℝ}}^2,
```

```math
\widehat c(\widehat E_j[I])=H^jd_I,
\qquad
\mathrm{val}(\mathsf{\text{𝖥}}_j[I])=qH^jd_I.
```

**命题 12.2（确定模式的像上反查与一般遗忘）。** 对固定已知 $`j`$，所选代表编译、五点占位编码和五点组成编码都在自己的像上单射，可以反查 $`I`$。这些像上反查不定义任意原始树到位置选择的函数，也不恢复任意来源的叶序或括号。

证明。五个 $`d_I`$ 互异；$`H^j`$ 可逆，因此不同选择的实际组成也互异，所选树更不能相等。占位五点也互异，空贡献又独立于非空树。故在各自有限像上都有逆表。零层树 $`\langle\alpha,\beta\rangle`$ 是合法原始树，却不在零层所选代表像中；而它和 $`\langle\beta,\alpha\rangle`$ 组成相同。于是组成映射在全树域不单射，像上选择反查不能扩展为不依赖额外选择规则的全树提取。不同括号也会被组成相加忘掉。∎

因此“原始 FIB 树到选择项”的说法只有在先声明窗口、选择参数或具体选择器时才有意义。本卷采用的是已有生成链加外给合法选择的前向编译；它没有从任意树读取选择的隐含接口。

**命题 12.3（统计关系链和任务下降）。** 对归一化经典单窗律，完整的摘要链与恢复链为

<table><tbody><tr><td>

```math
(p_{\varnothing},p_1,p_2,p_3,p_{13})
\xrightarrow{\pi_{\mathrm{occ}}}(X,Y,Z)
\xrightarrow{L}(U,V),
```

</td></tr></tbody></table>

<table><tbody><tr><td>

```math
p\xrightarrow{\mathcal{\text{ℳ}}}(U,V,S,T)
\xrightarrow{\mathcal{\text{ℳ}}^{-1}}p.
```

</td></tr></tbody></table>

这里 $`\mathcal{\text{ℳ}}^{-1}`$ 的完整标签为“定理 8.2 的合法域逆式”，定义域是定理 8.2 所列的合法矩域。

两次均值压缩分别增加的遗漏是正方形方向和 FIB 组成方向：

<table><tbody><tr><td>

```math
\text{正方形关系：}\quad
\varnothing+13\longleftrightarrow1+3,
```

</td></tr></tbody></table>

<table><tbody><tr><td>

```math
\text{FIB 组成关系：}\quad
\varnothing+3\longleftrightarrow1+2.
```

</td></tr></tbody></table>

此处加法表示等权来源混合或线性响应比较，不许可在一个窗口占用非法相邻集合。四矩对同一初始化单窗律的两项声明任务给出

```math
(U,V,S,T)\longmapsto p
\longmapsto
\begin{cases}
\nu_p&\text{立即输入第三位置，包含拒绝},\\
\nu_{p,\mathrm{empty},3}&\text{先输入空窗，再输入第三位置}.
\end{cases}
```

证明。均值箭头由定义 6.1，核及其闭纤维由定理 6.2–6.4；矩箭头由定义 8.1，逆式由定理 8.2；任务箭头分别是命题 11.2 的确定表推前和定理 11.8 的确定表推前。所有箭头用同一个 $`p`$、已给初态、编译约定及动作历史。∎

关系卷定义 3.1–3.3 的任务原则在这里具体为：摘要足够，当且仅当所求目标在它的实际纤维上不变。第七节检验均值目标，第十一节逐回复事件检验分布目标。恢复后的 $`p`$ 支持这些固定表的推前；若新窗口为随机输入、自适应菜单或另一个来源，还须给真实联合、条件更新和取得合同。

**命题 12.4（完整单窗矩不恢复任意跨窗联合）。** 沿用关联卷定义 8.6、命题 8.7 的双窗来源，令 $`J_0=\varnothing,J_1=\{2\}`$，从高到低实际输入 $`J_A,J_B`$，其中 $`A,B\in\{0,1\}`$，并给

```math
P_\theta(0,0)=P_\theta(1,1)=\theta,\qquad
P_\theta(0,1)=P_\theta(1,0)=1/2-\theta,
\qquad 0\le\theta\le1/2.
```

每窗的完整律都是 $`(\delta_{\varnothing}+\delta_2)/2`$，四矩均为 $`(U,V,S,T)=(0,1/2,0,0)`$，共享接缝恒零；但同一读者的终值和随后实际空窗回复分别为

```math
13A+3B,\qquad 55A+13B.
```

在 $`\theta=1/2`$ 和零的两律中，终值支撑分别为 $`\{0,16\}`$、$`\{3,13\}`$，空窗后支撑分别为 $`\{0,68\}`$、$`\{13,55\}`$，完整分布不同。

证明。边缘中 $`P(A=1)=P(B=1)=1/2`$，且两种模式都不占低端或高端，所以所有路径合法、接缝恒零。组成在两步后为 $`H(0,A)^{\mathsf{\text{𝖳}}}+(0,B)^{\mathsf{\text{𝖳}}}`$，施加 $`q`$ 给首式，实际空窗再乘 $`H`$ 给第二式。两个参数端点分别只含同值对和异值对，得到所列支撑，故不同。∎

该反例的终值均值都为八，空窗后均值都为三十四；完整律不足并不否定这些特定均值任务的充分性。第十节的因子化合同或真实条件核可以补足相应任务所需的共同关系，不能从相同边缘和同名接缝自动得到。四矩补回单窗经典概率，没有把所有历史合并成一个局部模式。

**命题 12.5（附加相干来源的共同环境边界）。** 经典模式概率的恢复不决定相干历史中的非对角关系，也不决定以后重新接入的环境。按二阶卷命题 110.4，系统和环境均为量子位，初态为 $`\varrho\otimes|0\rangle\langle0|`$，以系统控制、环境为目标的同一个 CNOT 记为 $`W`$。一次作用后忽略环境，系统通道为

```math
\mathcal{\text{𝒟}}_Z(\varrho)=\frac{\varrho+P_z\varrho P_z}{2}.
```

第二次使用同一个环境恢复原联合态；两次各用新环境则仍给 $`\mathcal{\text{𝒟}}_Z(\varrho)`$。

证明。$`W|j,0\rangle=|j,j\rangle`$，首次联合态为 $`\sum_{j,k}\varrho_{jk}|j,j\rangle\langle k,k|`$；环境迹消去不同指标的项，给去相位。共同环境下 $`W^2=I`$，故第二次恢复原态。新环境下两次约化复合为 $`\mathcal{\text{𝒟}}_Z^2=\mathcal{\text{𝒟}}_Z`$；例如系统初态 $`|+\rangle`$ 时，两结论不同。∎

此例只用具名实现和允许再次作用的环境，不能据单窗概率或三维占位图推得物理相干实验。第二节的次序表示、共同相位参照、受控比较及本命题的环境权限各有自己的来源合同；恢复 $`p`$ 不恢复这些未声明的接口。

## 综合：保留生成、选择与仍被任务使用的关系

**定理 13.1（选择项演算的任务分层综合）。** 在完整有序 FIB 替换、非负窗口尺度、所选编译约定、归一化经典单窗律及第十一节初始化原生读者的合同内，以下三个问题分别有明确答案：

<table><tbody><tr><td>

```math
\text{怎样生成来源？}
```

</td></tr></tbody></table>

```math
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,\quad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle;
```

<table><tbody><tr><td>

```math
\text{怎样合法选择与接续？}
```

</td></tr></tbody></table>

```math
I\in\mathcal{\text{𝒮}}=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\},\quad
s\,h(I)=0,\quad s'=\ell(I);
```

<table><tbody><tr><td>

```math
\text{怎样保留仍被读出消费的关系？}
```

</td></tr></tbody></table>

```math
\left(
\mathbb{\text{𝔼}}_p[\xi],\mathbb{\text{𝔼}}_p[\eta],
\mathbb{\text{𝔼}}_p[\xi(\xi-1)],\mathbb{\text{𝔼}}_p[\xi\eta]
\right)\longleftrightarrow p.
```

来源生成使第三位置的组成等于前两位置组成之和；受限选择使第一、第三位置可以联合占用，从而形成正方形底面。两关系分别产生组成核与正方形核，不相互代替。四矩恢复全部单窗概率，并在第十一节的声明历史上给出立即第三位置的完整拒绝回复、奇偶记录条件回复和空窗后第三位置的完整合法回复。

证明。生成由定义 1.1 和结构归纳；合法集合由定理 1.3，部分合并由定义 3.1，续接由定理 10.2。两关系及其不同层次由命题 5.3，全部纤维及退化由定理 6.2–6.4。任意平均目标的系数判据由定理 7.2–7.3；矩恢复与合法域由定理 8.2。立即任务由定理 11.4–11.5，另一实际取得与消费路径由定理 11.7–11.8；每一步使用同一来源或明确声明的不同动作路径，故可以组合。∎

位置记法把二、三、五、七退回到更原始的结构：一条来源生成链上的三个位置，以及唯一允许的双位置联合。金字塔由选择关系产生，梯形由组成读出产生；完整概率还要保留共同出现的关系，递归任务还要求这些关系在真实接缝和历史之后继续可用。均值的维数、守卫的状态数、精确样本记录和未知律的取得分别对应不同任务，不相互冒领。

最终关系链应连同选择参数书写：

<table><tbody><tr><td>

```math
\begin{aligned}
\alpha&\xrightarrow{\tau}(T_n)_{n\ge0}
\xrightarrow{\mathrm{win}_j}(A_j,B_j,C_j),\\
(j,I,\text{编译约定})
&\xrightarrow{\sigma_j}\mathsf{\text{𝖥}}_j[I]
\xrightarrow{\widehat E_j}\text{所选有序来源或独立空贡献},\\
p\in\Delta_4&\xrightarrow{\mathcal{\text{ℳ}}}(U,V,S,T)
\xrightarrow{\mathcal{\text{ℛ}}}(\nu_p,\nu_{p,\mathrm{empty},3}).
\end{aligned}
```

</td></tr></tbody></table>

三行中的符号分别保留以下完整标签：$`\tau`$ 为“生成完整轨道”，按定义 1.1 生成轨道；$`\sigma_j`$ 为“合法位置选择”，沿用定义 12.1 的位置标签映射；$`\mathcal{\text{ℛ}}`$ 为“已声明的同历史任务”，其两分量分别依照第十一节两条已声明动作历史给出回复律。

第一行的窗口族按定义 1.2 从整条轨道取指定索引，不是从一棵任意 $`T_n`$ 逆推出窗口或选择；第二行把该族作为已给来源环境。确定模式的像上反查、均值纤维、精确总体矩、实际经验记录和附加相干权限都保持各自范围。普通证明覆盖声明的数学域，不由有限样本、几何图像或来源引文扩张成未给出的操作能力。

## 追加锚（本行以下为增补区）

## 十四、规范来源的展开、共享与纯解释成本

**定义 14.1（同源子树共享）。** 沿用定义 1.1 的自由有序树及完整替换。$\operatorname{Sub}(t)$ 是 $t$ 中各节点及其全部后代构成的有序带标号子树集合；叶标签、左右端口及括号均参与相等判断。$D(t)$ 只合并完全相同的这种子树，根仍代表 $t$，不保留不从根可达的轨道项。经典的 minimal-DAG 原理是“一个不同的 fringe subtree 对应一个节点”，见 Seelbach Benkner–Wagner, *Distinct Fringe Subtrees in Random Trees*, [§1，期刊页 3687](https://doi.org/10.1007/s00453-022-01013-y)。这里使用该表示原理，不使用其随机树渐近定理；以下计数针对本卷指定的 $T_n$。

**定理 14.2（规范 FIB 来源的精确共享及解释）。** 定义 1.1 的 $T_n$ 有 $\mathrm{Fib}_{n+1}$ 个叶及 $2\mathrm{Fib}_{n+1}-1$ 个展开节点。纯根 DAG 满足

$$
|D(T_n)|=
\begin{cases}
1,&n=0,1,\\
n+1,&n\ge2.
\end{cases}
$$

若 $E$ 是确定的纯结构解释，且 $E(\langle s,t\rangle)=\mu(E(s),E(t))$，则以已给的两个叶值为起点，$E(T_n)$ 可用 $\max(n-1,0)$ 次 $\mu$ 调用求出。这里的调用数不是不计表示长度的位时间界。

证明。沿用定义 1.1 已有的递推，叶数满足初值 $L_0=L_1=1$ 及 $L_{n+2}=L_{n+1}+L_n$，故 $L_n=\mathrm{Fib}_{n+1}$。满二叉树的内部节点数为叶数减一：每个内部节点贡献两条边，而树的边数等于总节点数减一。因此总节点数为 $2L_n-1$。

$\operatorname{Sub}(T_2)=\{T_0,T_1,T_2\}$。对 $n\ge2$，根的两个子树为 $T_{n-1},T_{n-2}$；归纳给

$$
\operatorname{Sub}(T_n)=\{T_0,T_1,\ldots,T_n\}.
$$

$T_0,T_1$ 是不同标号的叶，其后叶数严格增加，故这些树互异。由定义 14.1 的经典共享原理得到 $n+1$ 个节点。$n=0,1$ 时只有根叶，不能把未出现的另一个叶计入。另由 $\mathrm{Fib}_{n+3}\ge2\mathrm{Fib}_{n+1}$，展开规模对层数至少指数增长，而共享节点数线性增长。

令 $e_0=E(\alpha),e_1=E(\beta)$，并对 $2\le k\le n$ 计算 $e_k=\mu(e_{k-1},e_{k-2})$。结构递推和归纳给 $e_k=E(T_k)$，每个复合轨道项仅组合一次；$n\le1$ 时直接取相应叶值。共享合法的条件是相同子树的解释确实相同；依赖出现位置、外部历史、可变环境或副作用的操作不满足这个纯解释假设。

设 $b_k$ 是 $e_k$ 的实际编码长度，$c_\mu(u,v)$ 包含读取操作数、组合及写出结果的位成本。总成本应计入所需叶值的取得、索引及存储管理、$\sum_{k=2}^n c_\mu(e_{k-1},e_{k-2})$ 和所要求输出的写出成本；非空求和只在 $n\ge2$ 出现。只有在全部中间编码长度及相应操作成本有多项式界时，这才给出对 $n$ 的多项式位时间界。若输入只有二进制 $n$，对 $n$ 线性的组合数不等于对 $\log(n+1)$ 的多项式时间。若请求的是展开树而非其纯解释或共享表示，仍须写出 $2\mathrm{Fib}_{n+1}-1$ 个节点。共享和依赖调度分别承担不同条件；固定纯 DAG 的拓扑重排及成本不变性见 [Bryant 文献注 §1](../../../Library/ConceptDynamics/bryant1986boolean.md#1-three-orders-and-the-cost-of-a-fixed-pure-dag)。∎

## 十五、附加非空规则的逻辑端口与全局补全

**定义 15.1（非空端口扩展及其边界）。** 以定义 5.1 的占位编码记

$$
\Sigma=\{(x,y,z)\in\{0,1\}^3:xz=yz=0\},\qquad
\Sigma^+=\Sigma\setminus\{(0,0,0)\}.
$$

坐标始终是低、高、中；印刷次序始终是低、中、高，即 $(x,z,y)$。五项对应为

| 选择项 | 旧零层标签 | 印刷词 | $(x,y,z)$ |
| --- | --- | --- | --- |
| $\mathsf{\text{𝖥}}[\varnothing]$ | $[null]$ | $000$ | $(0,0,0)$ |
| $\mathsf{\text{𝖥}}[1]$ | $[2]$ | $100$ | $(1,0,0)$ |
| $\mathsf{\text{𝖥}}[2]$ | $[3]$ | $010$ | $(0,0,1)$ |
| $\mathsf{\text{𝖥}}[3]$ | $[5]$ | $001$ | $(0,1,0)$ |
| $\mathsf{\text{𝖥}}[1,3]$ | $[25]$ | $101$ | $(1,1,0)$ |

$\Sigma$ 是离散关系，定理 5.2 的 $\mathcal{\text{𝒫}}=\operatorname{conv}(\Sigma)$ 是均值凸体；把均值当作单个布尔门的输入不是本定义。$\Sigma^+$ 的非空条件 $x\lor y\lor z=1$ 是附加规则，删除了原来合法的空窗。

扩展电路另行供应有限显式无环连线、全部命名主输入、每个内部信号的唯一生成门及指定输出；每个门以 $x,y$ 为输入端口、$z$ 为输出。同一全局变量可以扇出，也可同时接到一个门的两个输入。常量端口、输入钉值及强制输出为一属于明确附加能力。它们均不由定义 10.1 的原生接缝取得。编码和总验证合同取 [Cook 文献注定义 5.1](../../../Library/ConceptDynamics/cook2006pversusnp.md#5-explicit-nor-circuits-and-boundary-tasks)。

**定理 15.2（选择端口到经典补全语言的逐赋值对应）。** 在定义 15.1 的附加合同下，每个单元的关系恰为 $z=\neg(x\lor y)$。对相同连线的 NOR 电路，以每门的三个信号填写本卷占位端口，给出保持每个主输入赋值、全部内部信号及目标输出的双向对应。因此经典 NOR 电路的求值、目标补全及前缀完成纤维，分别对应扩展选择网络的同名任务。

保留原 $\Sigma$ 时，若另给有限简单图 $G=(V,E)$、常量零端口及每个顶点只计一次的目标 $\sum_v u_v\ge K$，把边 $\{v,w\}$ 接成 $(x,y,z)=(u_v,0,u_w)$，则合法完成逐赋值对应图的大小至少 $K$ 的独立集。这是另一种附加网络，不是非空门网络。

证明。$x=1$ 或 $y=1$ 时，排斥式迫使 $z=0$；$x=y=0$ 时，附加非空式迫使 $z=1$。反向逐输入检查也都满足排斥及非空式，故四个输入各有唯一输出。在原五点函数代数中，逐点检验给空窗指标

$$
e_{\varnothing}=1-x-y-z+xy.
$$

附加 $e_{\varnothing}=0$ 正好给 $z=1-x-y+xy=(1-x)(1-y)$；联合项 $xy$ 在此是同一模式上的乘积。NOR 的常数大小 NOT、OR、AND 表达式及二元门的受限最小性，是 [Cook 文献注命题 5.2](../../../Library/ConceptDynamics/cook2006pversusnp.md#5-explicit-nor-circuits-and-boundary-tasks) 中归属于经典布尔演算的中间步骤。它们不赋予原生 FIB 树任意连线权限。

对扩展网络，一个主输入赋值沿所给拓扑序唯一决定全部输出。每个门的关系正是刚证明的 $\Sigma^+$ 等式，故电路赋值必给合法选择赋值；反向对同一拓扑序归纳，合法选择赋值只能给这些电路信号。对应不复制变量的值，也不把不同局部门的见证拼为一个虚构赋值。固定前缀只是把同一对应限制到这些主输入，因而保持整个完成集合。

在原五态边网络中，两式变为 $u_vu_w=0$ 及 $0u_w=0$；第一式恰排斥两个相邻顶点同时入选。共享端口使用同一个 $u_v$，目标计顶点而非出现次数，遂给独立集的精确对应，包括空图和阈值边界。

这里使用的经典复杂度结果及完整归约属于 [Cook 文献注 §§6–8](../../../Library/ConceptDynamics/cook2006pversusnp.md#6-completion-and-cardinality-with-classical-reductions)：显式电路正向求值在 P，输出一补全在 NP 中且由 3-SAT 得 NP 完全性，给定拓扑序也保持该归约；原五态阈值任务由子句相容图的经典归约得 NP 完全性。把该等价逐赋值运输到当前端口产生本定理的源特定后果。只有原 $\Sigma$ 及一致的钉值、没有基数目标时，未钉变量全置零即可完成，只需检查已钉一之间的冲突；不能把这一简单任务误作阈值任务。∎

## 十六、受限原生链的转移与完成观察的合同

**定义 16.1（仅有局部限制的原生链）。** 固定显式窗口数 $L$、定义 10.1 的高到低读向、旧外接缝及末端许可。每窗另给一个显式允许集合 $A_i\subseteq\mathcal{\text{𝒮}}$；它可以排除空窗或钉住本窗位置，但不把远处端口认作同一变量。固定交换半环 $S$，给每个允许模式可计算的权 $w_i(I)\in S$ 及端点列向量 $\lambda,\mu$，实际路径权必须是

$$
\lambda(s_0)\mu(s_L)\prod_{i=1}^L w_i(I_i),\qquad
I_i\in A_i,\quad s_{i-1}y(I_i)=0,\quad s_i=x(I_i).
$$

排除的模式权为零；非法尝试另回复 $\bot$，不与合法零数量混同。所声明乘积分解约束的是同一完整路径的权，不是从单窗边缘推断的随机独立性。

**命题 16.2（附加局部规则仍保持两活态上界）。** 定义 16.1 的路径总权为

$$
\lambda^{\mathsf T}K_1^{A_1}\cdots K_L^{A_L}\mu,
\qquad
K_i^{A_i}(s,t)=
\sum_{\substack{I\in A_i\, :\, sy(I)=0\\x(I)=t}}w_i(I).
$$

它只需 $O(L)$ 次半环运算；在系数、端点和所有中间值的表示长度与运算成本有多项式界时，位时间也为多项式。每一已知窗口层至多有两个活接缝态，窗口索引及该层的限制另属显式输入，失败另列；某些限制可使其中一个不可达或可合并，故不对受限链重复宣称最小值恰为二。

证明。每窗仅五种模式，可在常数次半环运算内逐接缝填核。定义 10.1 的唯一跨窗约束仍是 $s_{i-1}y(I_i)=0$；改变 $A_i$ 不增加跨界变量。命题 10.6 的同路径分配律证明遂原样适用，空链为 $\lambda^{\mathsf T}\mu$。固定二阶矩阵的逐窗乘法给线性运算数，实际位复杂度再计各次系数运算及输出。

若 $w_i(I)=a_i^{x(I)}b_i^{z(I)}c_i^{y(I)}$ 且 $A_i=\mathcal{\text{𝒮}}$，恰回到命题 10.4 的 $B(c_i)B(b_i)B(a_i)$；任意模式限制不自动仍有该三因子形式，应使用上面的有限和，半环中不以减法删除模式。自然数半环计算计数，布尔半环计算可行性，最大加半环计算可加局部分数的最大值，其中不可行为 $-\infty$。非负实权须有正总权才能归一化为概率；任意相关来源必须供应真实条件核或足够联合状态，并保留拒绝质量，见命题 10.8。全一权的 $\mathrm{Fib}_{3L+2}$ 只属于定理 10.7 的初接缝零、末端自由、单位位零、允许高端空填充且无 End 动作的开放端合同；局部限制或其他端点均须重新乘相应核。

受限链的 P 上界不排斥它在 $P=NP$ 时也为 NP 困难；这里不给出 P 与 NP 的分离。定理 15.2 的任意共享网络增添了本定义没有的跨窗相等约束及目标。一般切口须保留同时未决的全部变量关系，显式联合表在 $w$ 个布尔活变量上有至多 $2^w$ 行，失败另列；已有完整消元构造及成本属于 [Dechter 文献注命题 1–3](../../../Library/ConceptDynamics/dechter1996bucket.md)。这只是该显式表示的规模，不能据此推出所有简洁程序的下界。∎

**定义 16.3（完成观察及已有供应的适用范围）。** 对定义 15.1 的扩展电路，完成观察者自己选择主输入前缀 $b$。其全历史纤维、下一步预测和增长，取 [Cook 文献注 §7](../../../Library/ConceptDynamics/cook2006pversusnp.md#7-whole-prefix-fibres-prediction-and-terminal-growth) 的 $\Omega_{\mathcal C}(b)$、$E(\mathcal C,b)$、$\Lambda_{\mathcal C}(b)$ 和非终端增长规则；在完整长度直接验证并停止。完成图的语义存在不提供一次免费查表操作。对整个电路族统一构造、解址并执行成功顺序的资源条件，取该注 §8；允许多项式长度的状态和程序，不要求精确残余等价类只有多项式多个。该注 §9 的开放条件与普通 $P=NP$ 恰等价，不在这里另设一个独立猜想。

固定未知实际来源的读取是另一合同：定理 10.2 仅最小化合法后缀语言的两个活态；数量读者是定义 11.1 的 $(s,C)$，其中 $C'=HC+d_I$，不是只有 $s$。对固定单窗归一化经典律，定理 6.2 给全部占位纤维及 $\kappa$ 的闭端点，定理 7.2 给任意目标的联合系数 $\Lambda_f$：非退化占位纤维上只有该系数为零才可遗忘 $\kappa$，退化单点无此必要条件。命题 11.3 的同均值两律在同一初始化、紧接第三位置的实际历史下有不同完整回复律；无条件拒绝率在那一对律上却相同。定理 11.4–11.8 的恢复和条件化均保留同一来源、指定动作词及正概率事件，不能用另一次重置试验替代该历史。

完整局部律也不自动供应共同全局完成：[局部填充卷 §12](AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md#12-c5-的局部一致全局失败示例) 的逐位重叠五环窗口有相同完整二元组边缘及单点局部 $\kappa$ 纤维，却没有一个共同合法全局分布。该有限反例只否定所给局部资料的全局充分性，不是计算复杂度下界。任意跨窗联合及附加相干环境的界限另由命题 12.4–12.5 持有；单窗恢复不改变这些界限。

[有限表分类卷](FIB_NATIVE_FINITE_TABLE_COMPLEXITY_CLASSIFICATION.md) 引理 6.1–6.2 使用固定原生字面查询在同一实际来源定义一致布尔变量，并供应每个赋值的实际有限见证；CNF 的 $M$ 个文字出现编译成最多 $M$ 次调用的四回复求值图。定理 7.3 的 BOTH-PREPARER 下界已可用所有来源上终止的无环准备器实现。其定理 11.1 只在整张服务表及入口字面固定、仅二进制上限变化的 acquired-selector 语言给 P 上界，不给变化表族统一多项式预处理。它们的量词、输入语言、完整来源域、原始入口、预算与取得权限各归原条目；此处的对应是“一个给定来源的求值”和“存在来源达到输出”的量词区别，不是从四回复图向任意 NOR 连线的原生安装定理。

## 追加锚（本行以下为增补区）

## 十七、AURIC–NOR 完成关系的有限域二次适配

**定义 17.1（有效二次约束实例）。** 取定义 15.1 的显式扩展网络 ​$C$，其全局信号线集合为 $V(C)$，主输入为 $w_1,\ldots,w_m$，门数为 $g$，边界、钉值和输出要求均是编码的一部分。选定一个具有有效元素编码、加乘和等式比较算法的有限域 $\mathbb F$。域表示的位复杂度、门引用、输入名和边界的总长度均计入 $N$；不允许把一个大数值的输入个数作为未展开的免费参数。

对每条线 $v$ 引入 $Z_v\in\mathbb F$，加入布尔性约束

$$
Z_v(Z_v-1)=0.
\tag{34}
$$

对每个按给定拓扑序排列的 NOR 门 $a,b\to c$，加入

$$
(1-Z_a)(1-Z_b)-Z_c=0.
\tag{35}
$$

主输入钉值、常量线和指定输出分别写成线性等式；若边界彼此冲突，则该实例的解集定义为空（实现上可直接拒绝，或加入一行 $0=1$），而不是把没有边界可满足性的约束集合误当作空集。若 $m=0$，主输入词是唯一的空词。

**定理 17.2（逐赋值的二次适配）。** 对每个有效网络 $C$，约束 (34)–(35) 及其边界解与满足同一边界的布尔电路赋值一一对应。给定主输入后，所有内部线值唯一；反向，任一约束解的每个线值都是 $0$ 或 $1$，并且满足原网络的全部门和边界。约束行数、变量数和稀疏非零项数为 $O(|V(C)|+g+\text{边界数})$，并可在 $N$ 的多项式时间内构造。

**证明。** 在任意域中，$Z(Z-1)=0$ 的根只能是 $0,1$，故 (34) 给出布尔性。对布尔输入，(35) 等价于 $Z_c=(1-Z_a)(1-Z_b)=\operatorname{NOR}(Z_a,Z_b)$，而此前的端口定理已将该式与附加非空选择网络逐赋值对应。按拓扑序归纳，每个门输出由其两个输入唯一决定；因此每个主输入至多有一个内部扩展。反向，约束解的布尔性和 (35) 逐门给出同一个递归扩展，边界等式保持不变。每行只含常数个变量和常数个域运算，故构造规模与时间均受上述界控制。若网络畸形、引用越界或拓扑序不满足边关系，则按定义拒绝而不产生一个伪约束实例。∎

把一个常数坐标 $Z_0=1$ 加入变量向量后，(34)–(35) 可按标准形式写成稀疏 R1CS：每行都是

$$
(AZ)\circ(BZ)=DZ,
\tag{36}
$$

其中 $A,B,D$ 的非零项由门引用和边界直接生成。这里采用 Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, [§8.4](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) 的稀疏算术电路翻译接口；该文献的证明系统、承诺和模拟器是另一个合同，本适配本身不声称已经得到零知识协议。

**命题 17.3（均值模型不能替代实际门值）。** 对完整五态关系 $\Sigma$，设各模式概率为 $p_I$，空模式概率为 $p_\varnothing$，并令

$$
X=\mathbb E[x],\quad Y=\mathbb E[y],\quad Z=\mathbb E[z],\quad \kappa=\mathbb E[xy].
$$

则逐模式关系的期望满足

$$
Z=1-X-Y+\kappa-p_\varnothing.
\tag{37}
$$

在非空支持 $\Sigma^+$ 上，$p_\varnothing=0$，所以

$$
Z=(1-X)(1-Y)\quad\Longleftrightarrow\quad \kappa=XY.
\tag{38}
$$

在完整五态域上，(37) 与 $Z=(1-X)(1-Y)$ 等价于 $\kappa-XY=p_\varnothing$，而不是同时要求空模式和协方差都为零。

**证明。** 对每个模式有 $z=1-x-y+xy-\mathbf 1_{I=\varnothing}$。取期望即得 (37)；整理后得到 (38) 及完整域的等价式。反例是 $p_\varnothing=1/4$、$p_{\{1,3\}}=1/2$、$p_{\{2\}}=1/4$（按本卷低—高—中坐标），此时 $X=Y=1/2$、$Z=1/4$、$\kappa=1/2$，等式 $Z=(1-X)(1-Y)$ 成立但 $p_\varnothing\ne0$。因此把概率均值直接代入 (35) 会额外假设独立性并丢失联合项。∎

**资源边界。** 定理 17.2 是离散线值的逐赋值保持定理。它不把实数精确运算变成有限比特的高效算法，也不把有限域约束系统自动变成承诺、交互或知识提取协议。若要把约束用于证明系统，必须另行给出域元素的编码、承诺随机性、验证者挑战、失败分支和总成本；共享线仍由一个全局变量表示，不能把局部门的局部见证拼成不同的同名线值。该适配只补足从本卷附加端口到二次关系的接口，NP 完全补全和因果选择的复杂度量词仍取 [Cook 文献注 §§6–9](../../../Library/ConceptDynamics/cook2006pversusnp.md#6-completion-and-cardinality-with-classical-reductions) 的已声明范围。

## 追加锚（本行以下为增补区）

## 十八、从接缝计数到成功条件化的原生生成

本节把定理 10.7 和命题 16.2 的实际链计数接到成功路径生成。
一般的后向成功函数、Doob 条件化、重试与轨迹 KL 恒等式使用
[Chetrite–Touchette 文献注](../../../Library/Computability/chetritetouchette2015conditioned.md)
的有限模型；本节的新增综合是五模式接口上的整数取得过程、两窗精确权重和失败质量对应。
这些是散文模型中的推导，未在此交付 Lean 证明；不主张一般条件化方法的原创性。

**定义 18.1（受限链的后向完成数）。** 固定定义 16.1 的显式 $L$ 窗、
允许集合 $A_i$、初接缝 $s_0$ 及末端许可 $B\subseteq\{0,1\}$。
不附加跨窗共享变量。以 $t$ 表示已经输入的窗口数，令

$$
n_L(s)=\mathbf1_{s\in B},\qquad
n_t(s)=\sum_{\substack{I\in A_{t+1}\\sy(I)=0}}n_{t+1}(x(I))
\quad(0\le t<L).
$$

每个形式窗口原先独立均匀提议五模式；不在允许集合或违反守卫的提议进入失败吸收态。
成功指全部 $L$ 窗通过并满足末端许可，不另要求证出全局目标。

**定理 18.2（由完成数取得原生条件生成）。** 当 $n_0(s_0)>0$ 时，
在正完成数状态按以下概率选择各个模式：

$$
q_t^*(I\mid s)=
\begin{cases}
n_{t+1}(x(I))/n_t(s),&I\in A_{t+1},\ sy(I)=0,\\
0,&\text{其余情形}.
\end{cases}
$$

所得整词分布是对全部成功词的均匀分布，每词概率为 $1/n_0(s_0)$。
初始化、全部后向表和一条成功词可在 $L+1$ 的多项式位时间内确定性取得；
精确均匀采样另有期望多项式位成本，不承诺公平随机位下的有限最坏采样界。

**证明。** 每个合法下一模式唯一确定新接缝，按该模式分组全部完成词即得定义 18.1；
归纳得到 $n_t(s)$ 恰为剩余完成数，且 $0\le n_t(s)\le5^{L-t}$。
原提议的成功函数是 $h_t(s)=n_t(s)/5^{L-t}$，故文献注 §1 的
$q_t h_{t+1}/h_t$ 正是所列模式概率。沿完整成功词相乘，所有中间计数消去，
终值 $n_L=1$ 给 $1/n_0(s_0)$。零完成数分支不会被选择。

每层两项计数，各由至多五项相加取得，中间整数有 $O(L+1)$ 位；
扫描显式允许集合、计算整表、存储和重建词均为多项式成本。
若只需一条词，每步选首个合法且子计数为正的模式即可，输出并检查全部窗口和末端。
若要求精确均匀采样，在 $\{0,\ldots,n_t(s)-1\}$ 上均匀取整数，
按各模式的子计数分段。用 $k=\lceil\log_2 n_t(s)\rceil$ 个公平位提出整数，
超界重试；$n_t(s)=1$ 时不用随机位，其余每轮接受率大于 $1/2$。
每层期望常数轮、每轮 $O(L+1)$ 位及多项式整数操作，总期望成本多项式。
拒绝采样的轮数没有确定的有限上界；给定有限截止则需另计失败概率。∎

**命题 18.3（开放两窗的精确导航权）。** 取定理 10.7 的初接缝零、末端自由、
允许高端空窗、无额外 End 动作合同，令 $L=2$。则

$$
(n_1(0),n_1(1))=(5,3),\qquad n_0(0)=21.
$$

第一模式按 $\varnothing,\{1\},\{2\},\{3\},\{1,3\}$ 排列的条件概率为

$$
\frac1{21}(5,3,5,5,3).
$$

二十一个合法词各有概率 $1/21$，原独立均匀提议的通过率为 $21/25$。

**证明。** 由定义 10.1，接缝零允许五模式，接缝一只允许空、第一和第二模式；
故一窗完成数是 $5,3$。第一窗有三模式进入零、两模式进入一，得到
$3\cdot5+2\cdot3=21$。代入定理 18.2 即得逐模式权；
接缝零的第二窗每模式概率 $1/5$，接缝一的三个合法模式各 $1/3$，两类乘积都为 $1/21$。∎

**推论 18.4（合法路径质量与取得成本）。** 在同一开放端合同下，
$L\ge0$ 个独立均匀五模式提议的成功率及其负对数为

$$
p_L=\frac{\mathrm{Fib}_{3L+2}}{5^L},\qquad
\mathcal I_L=L\ln5-\ln\mathrm{Fib}_{3L+2}.
$$

有 $p_0=1$，且当 $L\to\infty$，
$p_L=\Theta(((2+\sqrt5)/5)^L)$、
$\mathcal I_L=L\ln(5/(2+\sqrt5))+O(1)$。
定理 18.2 仍给期望多项式成本的精确条件生成以及确定性多项式成本的一条合法词。

**证明。** 定理 10.7 给成功词数，各原提议词概率均为 $5^{-L}$。
Fibonacci 的闭式给增长率 $\varphi^3=2+\sqrt5<5$。
文献注 §3 将 $\mathcal I_L$ 同时识别为成功域支撑分布到原提议的最小 KL。
因此原提议的低成功率与另一个可取得的高效生成器可以同时成立；
后者使用本链已给出的接缝完成数，不是从低成功率本身推出。∎

**任务扩展与经验的界限。** 若成功还要求一个几何证书或全局关系，须把它的
更新、合法性、终端检查和动作还原并入实际状态；两个接缝位不再自动充分。
[ML 白盒卷 §8](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md#8-从手写白盒到学习模型需要交换关系)
给输出、合法域及更新同时保持的解释合同，§16 给关键模式未见时的
$p(1-p)^N/4$ 精确识别风险及合法真标签查询的权限。它们不提供训练后策略的
统一成功率。经验提议器只有在每个实际失败历史后都保有成功概率下界时，才可用文献注 §2
的自适应重试界；整轨迹成功参考律的 KL 界则使用该注 §3，不以局部训练损失替代。

辅助对象可以由已有关系保守生成，具体构造语法、欧拉关系和固定深度枚举见
[AlphaGeometry2 文献注](../../../Library/Geometry/chervonyi2025alphageometry2.md)。
对这里的一般证书任务，成功域按“提议并在计入预算内产生通过验证的证书”定义，
成本包括经验库取得、提议、构造、推理和验证。SAT 的正支持、逆多项式随机成功率
及长度相关种子表分别使用 [Cook 文献注 §16](../../../Library/ConceptDynamics/cook2006pversusnp.md#16-successful-proposal-mass-completion-support-and-seed-tables)
的统一性条件；定理 18.2 的局部链算法不供应任意 SAT 的这些条件。

## 追加锚（本行以下为增补区）

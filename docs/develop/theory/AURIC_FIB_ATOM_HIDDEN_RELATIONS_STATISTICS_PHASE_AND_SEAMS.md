# FIB-ATOM：隐藏关系、统计相位与共享接缝

**约定 C-1.1（论域与来源）。** 本卷研究有限有序来源的指定观察任务。实概率、复 Hilbert 记录、另供的相干制备和原生数量读者分别给定；一层中的可实现性不授予另一层的操作。证明均为普通数学证明。共同五态接口取自不可变来源 [C-R1]–[C-R6]，本文以其原生任务为消费者，把单窗残差、统计敏感度、相位商和多窗循环接成同一条论证。既有理论作为注明出处的中间步骤使用；本文的任务连接不主张这些工具的原创性。

## 1. 五态、原始来源与实际读者

**约定 C-1.2（共同来源与标签）。** 原树、$`\rho`$、组成、$`M,S,q`$ 以及模式／旧标签／三种位序的完整字典使用 [A 卷 §1](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#1-有序原子五种选择与标准窗口)。固定 $`\Sigma=(0,1,2,3,13)`$，$`x`$ 低端、$`y`$ 高端、$`z`$ 中位，选择写 $`\mathsf{\text{𝖥}}[I]`$，标准数列写 $`F_n`$。空模式是实际窗口输入，分别区别于空词、未读取、原树零元及停止。

**约定 C-1.3（实际同源读者）。** 使用 [A 卷 §16](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#16-同一有序前缀的接缝余数组成图) 定义A-16.1的初始化、守卫、组成运输和吸收拒绝；明确允许菜单与守卫成功分开。实际空窗执行 $`C'=SC,s'=0`$；结束本文的有限合同不增设原生 End、复位或复制。原拥有者为 [C-R1] 定义1.1–1.3、7.1。

**接口 C-1.4（运输与遗漏）。** [A 卷 §1](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#1-有序原子五种选择与标准窗口) 命题A-1.2、A-1.4与 [A 卷 §5](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#5-完整组成更新与实际数量采样) 证明组成运输及其逆矩阵边界。组成和数量各有纤维；普通矩阵可逆不恢复树叶序、括号或任意逆替换。以下后继始终推送同一隐藏样本及其条件律。

## 2. 仿射回路、概率纤维与完整函数边界

**定义 C-2.1（单窗概率）。** 对实数 $`p_\sigma\ge0,\sum p_\sigma=1`$，按 $`\Sigma`$ 顺序记 $`p=(p_0,p_1,p_2,p_3,p_{13})`$，置


```math
X=\mathbb{\text{𝔼}} x,\quad Y=\mathbb{\text{𝔼}} y,\quad Z=\mathbb{\text{𝔼}} z,
\quad r=1-Z,\quad\kappa=\mathbb{\text{𝔼}}[xy],\quad
\Delta=r\kappa-XY.
```


**命题 C-2.2（底面回路与平面外顶点）。** 采用 [A 卷 §2](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#2-三均值关联纤维与目标差分) 的全部概率反解、闭纤维及退化分类，记宽度 $`w=\kappa_+-\kappa_-`$。同均值切向量 $`d=(1,-1,0,-1,1)^{\mathsf{\text{𝖳}}}`$ 张成唯一仿射回路。任意同一平面上的有限底面点 $`b_1,\ldots,b_N`$ 加一个平面外顶点 $`a`$ 后，全部仿射关系仍恰来自底面，每条关系中 $`a`$ 的系数均零。

**证明。** 五态齐次评价矩阵 $`(1,x,y,z)`$ 的四个非 $`13`$ 行可逆，故核一维，直接代入得 $`d`$。一般底面取仿射高度函数 $`\ell(b_i)=0,\ell(a)=1`$；把它作用于满足系数和零的关系，强制 $`\lambda_a=0`$，余项正是底面关系。齐次评价秩等于仿射维数加一，得到下表；加一个顶点提升仿射维数，却不消除已有底面混合歧义。$`\square`$

| 读出顶点 | 仿射维数 | 独立仿射关系数 |
| --- | ---: | ---: |
| 非退化三角形的三个顶点 | $`2`$ | $`0`$ |
| 正方形的四个顶点 | $`2`$ | $`1`$ |
| 方底锥的五个顶点 | $`3`$ | $`1`$ |

**命题 C-2.3（完整事件代数）。** [A 卷 §2](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#2-三均值关联纤维与目标差分) 命题A-2.5给五函数 $`1,x,y,z,xy`$ 的唯一目标展开与均值识别判据。它们还对逐点乘法闭合，并表示全部五态事件。

**证明。** 幂等与排斥 $`x^2=x,y^2=y,z^2=z,xz=yz=0`$ 将每个单项式降为五项。五个原子指示为


```math
e_0=1-x-y-z+xy,\quad e_1=x-xy,\quad e_2=z,
\quad e_3=y-xy,\quad e_{13}=xy.
```


它们逐点互斥、和一，给评价代数同构。这一闭合仅恢复五态经典函数律，未恢复原树或非对角相干。$`\square`$

**命题 C-2.4（联合正性完成布尔合法性）。** 置 $`\phi=(1,x,y,z,xy)^{\mathsf{\text{𝖳}}}`$。由逆式定义的实候选归一化律满足


```math
G=\begin{pmatrix}
1&X&Y&Z&\kappa\\
X&X&\kappa&0&\kappa\\
Y&\kappa&Y&0&\kappa\\
Z&0&0&Z&0\\
\kappa&\kappa&\kappa&0&\kappa
\end{pmatrix}
=V^{\mathsf{\text{𝖳}}}\operatorname{diag}(p)V,
\quad
V=\begin{pmatrix}
1&0&0&0&0\\1&1&0&0&0\\1&0&0&1&0\\1&0&1&0&0\\1&1&1&0&1
\end{pmatrix}.
```


因此 $`G\succeq0`$ 当且仅当全部 $`p_\sigma\ge0`$，且 $`\det G=\prod_\sigma p_\sigma`$。

**证明。** 每行是相应模式的评价；展开行列式得 $`\det V=-1`$。可逆合同把 $`G`$ 的正性等价地送到对角矩阵，行列式乘以 $`(\det V)^2=1`$。这是一份有限事件模型的完整认证，下面的较小残差 Gram 只给必要条件。$`\square`$

## 3. 共同底面残差、波动体积与四样本目标

**定义 C-3.1（实际 $`L^2`$ 残差）。** $`L^2(p)`$ 是五态函数按零范数等价取商的实内积空间。$`b=1-z`$ 是底面事件的指示，$`b^2=b,\mathbb{\text{𝔼}} b=r`$；它不是平均高度上的分数指示。$`r>0`$ 时取


```math
u=x-\frac Xr b,\qquad v=y-\frac Yr b.
```


**命题 C-3.2（残差与布尔界）。** $`\langle u,b\rangle=\langle v,b\rangle=0`$，并且


<table><tbody><tr><td>

```math
\|u\|^2=\frac{X(r-X)}r,\quad
\|v\|^2=\frac{Y(r-Y)}r,\quad
\langle u,v\rangle=\frac\Delta r,\quad
\Delta^2\le XY(r-X)(r-Y).
```

</td></tr></tbody></table>


底面条件协方差是 $`\Delta/r^2`$。最后的不等式不能代替完整概率合法性。

**证明。** $`xb=x,yb=y`$，展开各内积得到 $`X-X^2/r,Y-Y^2/r,\kappa-XY/r`$，再应用 Cauchy–Schwarz。对 $`Q_b=\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix}`$ 展开得 $`\det Q_b=\Delta`$，除以 $`r`$ 的条件表给协方差。候选 $`Z=0,X=1/4,Y=1/2,\kappa=5/16`$ 有 $`\Delta=3/16`$，$`\Delta^2=9/256\le12/256`$，却有 $`p_1=-1/16`$。它的残差矩阵可正，不能把该有符号候选称为实际概率 Hilbert 空间。$`r=0`$ 没有底面后验，直接使用唯一顶点律。$`\square`$

**命题 C-3.3（同均值纤维的响应体积）。** 对随机占位 $`R=(x,y,z)^{\mathsf{\text{𝖳}}}`$，


```math
C=\operatorname{Cov}R=
\begin{pmatrix}
X(1-X)&\kappa-XY&-XZ\\
\kappa-XY&Y(1-Y)&-YZ\\
-XZ&-YZ&Zr
\end{pmatrix}.
```


令 $`D=\det C`$。在 $`r>0`$ 时


<table><tbody><tr><td>

```math
D=\frac Zr\{XY(r-X)(r-Y)-\Delta^2\}.
```

</td></tr></tbody></table>


全部闭域上不用除法的式子为


<table><tbody><tr><td>

```math
D=Z(p_0p_1p_3+p_0p_1p_{13}+p_0p_3p_{13}+p_1p_3p_{13}).
```

</td></tr></tbody></table>


$`\operatorname{rank}C`$ 等于正质量顶点支撑的仿射维数；$`D`$ 是中心化响应 Gram 体积平方，区别于坐标金字塔固定体积 $`1/3`$。

**证明。** 使用 $`x^2=x,xz=yz=0`$ 得矩阵。把每个顶点补为 $`\widetilde v=(1,v)^{\mathsf{\text{𝖳}}}`$，置 $`H=\sum p_\sigma\widetilde v_\sigma\widetilde v_\sigma^{\mathsf{\text{𝖳}}}`$。减去均值的单位行列式消元给 $`\det H=D`$。Cauchy–Binet 在此可由行列式多线性直接展开：


```math
\det H=\sum_{|I|=4}\Bigl(\prod_{i\in I}p_i\Bigr)
\det(\widetilde v_i:i\in I)^2.
```


四底角共面给零，顶点加任意三底角的齐次行列式绝对值一，即四面体体积 $`1/6`$，得到四项式。代入逆式或对 $`z`$ 作 Schur 消元给含 $`\Delta`$ 式。又 $`a^{\mathsf{\text{𝖳}}}Ca=\sum p_i[a\cdot(v_i-\mathbb{\text{𝔼}} R)]^2`$，零空间恰为支撑差向量的正交补，证明秩式。若正底角数为 $`k`$，$`Z=1`$ 时秩零；$`Z=0`$ 时秩 $`\min(k-1,2)`$；$`0<Z<1`$ 时秩 $`\min(k,3)`$。故 $`D>0`$ 恰当且仅当顶点正且至少三底角正。$`\square`$

**命题 C-3.4（同均值支撑反例进入原生目标）。** 两律


```math
p^{(A)}=(0,1/3,1/3,1/3,0),\qquad
p^{(B)}=(1/6,1/6,1/3,1/6,1/6)
```


都有 $`(X,Y,Z)=(1/3,1/3,1/3)`$，但秩分别二、三，$`D`$ 分别 $`0,1/162`$。在 §6 的实际奇数档案后，下一高端请求的拒绝概率分别 $`0,1/4`$。

**证明。** $`A`$ 的三个支撑点在 $`x+y+z=1`$ 内且不共线；$`B`$ 的全支撑仿射三维。四项式给 $`B`$ 的 $`D=(1/3)4(1/6)^3=1/162`$。两者奇数质量 $`Y+Z=2/3`$，共同选择质量分别零、$`1/6`$，按 §6 表除以该正质量得拒绝概率。$`\square`$

**假设 C-3.5（四次独立同律制备）。** 另供四次真实 IID 五态制备及四个实际返回顶点，定义其四面体体积平方 $`T=V_{\rm tet}^2`$。该资源与原生同一个隐藏样本的继续分开。

**命题 C-3.6（体積补全的可执行统计目标）。** 此合同下


<table><tbody><tr><td>

```math
T\in\{0,1/36\},\quad \Pr(T=1/36)=24D,\quad
\mathbb{\text{𝔼}} T=\frac23D.
```

</td></tr></tbody></table>


固定 $`0<Z<1,0<X,Y<r`$ 时，$`\kappa_*=XY/r`$ 唯一同时最大化 Shannon 熵和 $`D`$。上述 $`A,B`$ 的 $`\mathbb{\text{𝔼}} T`$ 分别 $`0,1/243`$。

**证明。** 四个不同顶点中，只有顶点加三个底角非零；每集合有 $`4!`$ 个独立样本顺序。用命题 C-3.3 展开得概率 $`24D`$，再乘 $`1/36`$。这是四样本函数，不是单响应的二阶矩。最大熵的普通中间步骤是固定边缘乘积补全：[C-R3] §§6、9 及相对熵非负给 $`H(p_*)-H(p)=\operatorname{KL}(p\Vert p_*)\ge0`$；因为 $`\log p_*`$ 在正底面为常数加 $`x,y`$ 势，在顶点单独定值，同均值消去交叉熵差。非负性可由 $`\log t\le t-1`$ 证明，等号仅相同律。内部 $`p_*`$ 全正且 $`\Delta=0`$，$`D=D_*-Z\Delta^2/r`$ 给唯一体积极大。$`Z=0`$ 时熵仍唯一最大，而三维 $`D`$ 沿整纤维恒零；侧面单点唯一，顶点直接处理。补全是模型选择，未断言真实未知律等于它，亦未断言它最保存已取得信息。$`\square`$

## 4. 从固定律残差到实际读口的统计信息

**定义 C-4.1（隐藏函数与正支撑）。** 对真实支撑 $`T=\{s:p_s>0\}`$，令 $`\mathcal{\text{𝒪}}=\operatorname{span}\{1,x,y,z\}\subset L^2(p)`$，$`w=xy`$，$`h=w-P_{\mathcal{\text{𝒪}}}w`$。先在四底角全正的域上定义


```math
\mathcal{\text{ℐ}}=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
```


顶点可以为零；对不存在的点不使用 $`d_s/p_s`$。

**命题 C-4.2（函数高度与保持均值的概率方向）。** 若四底角全正，$`\mathcal{\text{𝒪}}`$ 的支撑评价秩为 $`|T|-1`$，隐藏补一维，且


<table><tbody><tr><td>

```math
h_s=\frac{d_s}{p_s\mathcal{\text{ℐ}}}\ (s\in T),\quad
\|h\|_p^2=\frac1{\mathcal{\text{ℐ}}},\quad
\min_{g\in\mathcal{\text{𝒪}}}\mathbb{\text{𝔼}}_p(f-g)^2=\frac{J_f^2}{\mathcal{\text{ℐ}}}.
```

</td></tr></tbody></table>


若缺任一底角，评价秩为 $`|T|`$，$`h=0`$。固定支撑上的逐点表达与整五态上的逐点表达不同。

**证明。** 在四底角上，$`d`$ 消去 $`1,x,y,z`$，顶点系数零；故所给 $`h`$ 正交于 $`\mathcal{\text{𝒪}}`$，且 $`\|h\|^2=1/\mathcal{\text{ℐ}}`$、$`\langle w,h\rangle=1/\mathcal{\text{ℐ}}`$。评价核只有回路 $`d`$，证明余维一及 $`w-h\in\mathcal{\text{𝒪}}`$。任意 $`f`$ 的残差 $`J_fh`$ 给误差式。若缺底角，回路不能支撑于 $`T`$，故评价满秩。具体缺 $`13,1,3,0`$ 时分别在支撑上有 $`xy=0,y,x,x+y+z-1`$。缺顶点则四底角仍有回路，$`h`$ 不消失。更小、确定支撑一律用实际评价秩；不对缺失点除零。此结论是给定固定律的 $`L^2`$ 投影，未知律全闭纤维在端点仍可沿一侧引入零质量点；固定支撑双侧切线为零并不等于全纤维是单点。$`\square`$

**命题 C-4.3（条件独立下的隐藏高度与体积因子）。** 五态均匀律有 $`\Delta=0`$，但


```math
\mathcal{\text{ℐ}}=20,\qquad
h=xy-\frac{x+y}{2}+\frac{1-z}{4},\qquad\|h\|^2=1/20.
```


令 $`C_3=\operatorname{Cov}(x,y,z)`$，$`C_4=\operatorname{Cov}(x,y,z,xy)`$。全部真实支撑上有


<table><tbody><tr><td>

```math
\det C_4=\det C_3\,\|h\|^2=\prod_s p_s.
```

</td></tr></tbody></table>


**证明。** 均匀律 $`X=Y=2/5,Z=1/5,\kappa=1/5`$，$`h`$ 在四底角取 $`1/4,-1/4,-1/4,1/4`$，在顶点零，得式。对 $`G`$ 先消去常数列得 $`\det C_4=\det G`$。把最后函数换为 $`xy-P_{\mathcal{\text{𝒪}}}xy`$ 是单位行列式的基变换，因正交得到块对角 $`\operatorname{diag}(G_{\mathcal{\text{𝒪}}},\|h\|^2)`$；消去常数给 $`\det G_{\mathcal{\text{𝒪}}}=\det C_3`$。即使 $`\mathcal{\text{𝒪}}`$ 有相关列，正交投影仍存在、仍可选系数作上述变换，故乘积式成立，不能在奇异时改成行列式比或 $`0\times\infty`$。均匀律的独立是给定底面的条件独立，不消去联合事件函数方向。$`\square`$

**假设 C-4.4（完整结果或粗随机读口）。** 在规则不暗中依赖未知 $`\kappa`$ 的有限实验中，供应列随机矩阵 $`W(a\mid s)`$，实际结果分布 $`q_a=\sum_sW(a\mid s)p_s`$。完整模式读取是 $`W`$ 恒等的特殊资源合同。下述信息量按一份制备计算。

**命题 C-4.5（得分—残差等距与读口损失；经典信息几何 [C-L2] 的本纤维计算）。** 四底角全正时，完整结果的得分 $`\mathsf{\text{𝖲}}_s=d_s/p_s`$，顶点正时得分零。Fisher 信息是 $`\mathcal{\text{ℐ}}`$，且 $`h=\mathsf{\text{𝖲}}/\mathcal{\text{ℐ}}`$。一般有限正支撑、保留函数评价秩 $`a`$ 时，保持其均值的概率切向量 $`v`$ 经 $`v\mapsto v/p`$ 双射到保留函数的正交补，维数 $`|T|-a`$，内积为 $`\sum v_sw_s/p_s`$。实际读口满足


<table><tbody><tr><td>

```math
\mathcal{\text{ℐ}}_{\rm out}=\sum_{a:q_a>0}
\frac{(Wd)_a^2}{q_a}\le\mathcal{\text{ℐ}},\qquad
\mathcal{\text{ℐ}}-\mathcal{\text{ℐ}}_{\rm out}=\mathbb{\text{𝔼}}\operatorname{Var}(\mathsf{\text{𝖲}}\mid a).
```

</td></tr></tbody></table>


**证明。** 求 $`\log p_s`$ 导数得得分；其均值 $`\sum d_s=0`$，平方均值为 $`\mathcal{\text{ℐ}}`$。一般映射的保留函数内积为 $`\sum v_sf_s=0`$，反向 $`h\mapsto ph`$，故双射和内积成立。对输出求导，$`q'_a=(Wd)_a`$，$`q'_a/q_a=\mathbb{\text{𝔼}}(\mathsf{\text{𝖲}}\mid a)`$，方差分解给式。不损失当且仅当得分由实际结果可测；零输出信息当且仅当 $`Wd=0`$。正输入支撑上 $`q_a=0`$ 强制该输出全部 $`W(a\mid s)=0`$，故没有遗漏的非零导数项。较小固定支撑须用合法切向量 $`v`$ 替换 $`d`$。分别读取 $`x,y,z`$ 的输出律在固定均值纤维恒定；同一份样本共同保留 $`(x,y,z)`$ 则已识别模式。三均值、三种分别制备的单项结果、逐样本联合档案是不同信息。重参数化 $`\lambda`$ 使信息乘 $`(d\kappa/d\lambda)^2`$，因此 $`1/\mathcal{\text{ℐ}}`$ 的数值不是免费取得的比特数。$`\square`$

**命题 C-4.6（对角比、熵曲率与有限端点长度）。** 在正底面内部用自然对数置


```math
\vartheta=\log\frac{p_0p_{13}}{p_1p_3},\qquad H=-\sum p_s\log p_s.
```


则 $`\vartheta'=\mathcal{\text{ℐ}},H'=-\vartheta,H''=-\mathcal{\text{ℐ}}`$。平方根坐标 $`a_s=2\sqrt{p_s}`$ 位于半径二的球面，且


```math
\sum da_s^2=\sum\frac{dp_s^2}{p_s},\qquad ds_{\rm Fisher}^2=\mathcal{\text{ℐ}}\,d\kappa^2.
```


非退化仿射纤维的端点系数虽发散，弧长有限；整个弧长至多


```math
2\sum_{s\text{ 底角}}|\sqrt{p_s(\kappa_+)}-\sqrt{p_s(\kappa_-)}|.
```


**证明。** $`p_0'=p_{13}'=1,p_1'=p_3'=-1`$，逐个对数求导；熵导数中的常数因 $`\sum d_s=0`$ 消去。最大熵零斜率给 $`p_0p_{13}=p_1p_3`$，等价于 $`\kappa=XY/r`$，与 §3 一致。平方根微分直接给线元，$`\sum a_s^2=4`$。每个底角概率沿仿射纤维单调，速度的欧氏范数不超过各坐标速度绝对值之和，积分得到界；端点消失项形如 $`t`$，$`\int_0^\epsilon t^{-1/2}dt`$ 有限。单点纤维长度零。这仅证明该指定有限路径，不给任意振荡路径有限长度；概率球面属于分布几何。$`\square`$

## 5. 原生四矩的可行域、稳定反演与关系递推

**定义 C-5.1（一个初始窗口的同源统计）。** 从零态读一个随机模式，令其组成为 $`(\xi,\eta)=(x+y,y+z)`$。随后在同一状态实际追加空窗。响应为


```math
N_0=2\xi+3\eta,\qquad N_1=8\xi+13\eta.
```


另行供应精确总体矩，或有明确误差保证的估计


```math
\mu=(m_0,m_1,s_0,s_1)=(\mathbb{\text{𝔼}}N_0,\mathbb{\text{𝔼}}N_1,
\mathbb{\text{𝔼}}N_0^2,\mathbb{\text{𝔼}}N_1^2).
```


两相邻位置不是两次实验自动学到未知律；若精确首次数量档案已保留，$`0,2,3,5,7`$ 本已单射地标记确定模式。

**命题 C-5.2（四矩反演）。** 在此限定来源域上


<table><tbody><tr><td>

```math

\begin{aligned}
U=\mathbb{\text{𝔼}}\xi&=(13m_0-3m_1)/2,&V=\mathbb{\text{𝔼}}\eta&=m_1-4m_0,\\
A=\mathbb{\text{𝔼}}\xi^2&=(52s_0-3s_1+39V)/16,&
B=\mathbb{\text{𝔼}}\xi\eta&=(s_1-16s_0-25V)/16,\\
\kappa&=(A-U)/2,\qquad
p_{13}=\kappa,&p_3&=B-2\kappa,\\
p_2&=V-B+\kappa,&p_1&=U-B,&p_0&=1-U-V+B.
\end{aligned}
```

</td></tr></tbody></table>


**证明。** 五组成为 $`(0,0),(1,0),(0,1),(1,1),(2,1)`$，故 $`\eta^2=\eta,\xi^2-\xi=2xy`$。一阶系统 $`m_0=2U+3V,m_1=8U+13V`$ 的行列式二；平方系统 $`s_0=4A+12B+9V,s_1=64A+208B+169V`$ 的行列式六十四，求解得式。逐组成求质量给最后五式。这些等式不对任意其他初始状态或相关多窗来源自动成立。$`\square`$

**命题 C-5.3（归一化可行单纯形与误差运输）。** 合法矩域恰为五个顶点


```math
(0,0,0,0),\ (2,8,4,64),\ (3,13,9,169),\
(5,21,25,441),\ (7,29,49,841)
```


的四维单纯形。非归一化正测度的增广矩锥为 $`T\mathbb{\text{ℝ}}_+^5`$，其中 $`T`$ 各列为 $`(1,N_0,N_1,N_0^2,N_1^2)`$ 的模式评价，$`\det T=-256`$。归一化逆式可写 $`p=e_0+J\mu`$，


```math
J=\frac1{32}\begin{pmatrix}
120&-34&-32&2\\
8&2&32&-2\\
-588&145&84&-5\\
720&-176&-136&8\\
-260&63&52&-3
\end{pmatrix}.
```


若各矩误差分别不超过 $`\epsilon_{m_0},\epsilon_{m_1},\epsilon_{s_0},\epsilon_{s_1}`$，则逐分量 $`|\delta p|\le |J|\epsilon`$，且


<table><tbody><tr><td>

```math
\|\delta p\|_1\le53\epsilon_{m_0}+\frac{105}8\epsilon_{m_1}
+\frac{21}2\epsilon_{s_0}+\frac58\epsilon_{s_1}.
```

</td></tr></tbody></table>


**证明。** 增广矩是 $`Tp`$，展开其行列式或代入命题 C-5.2 得非零值，故五矩顶点仿射独立。$`p\ge0,\sum p=1`$ 的线性像正是所列单纯形，逆式非负是完整可行条件。整理逆式得 $`J`$，其列和零，故归一化自动保持。三角不等式和每列绝对和给误差界。带误差的数据须与该可行域相交后解释；截负再归一化不是这条精确反演。对任何已供应回复核，$`\operatorname{TV}(Kp,K\widetilde p)\le\|p-\widetilde p\|_1/2`$。若某分支的真实质量 $`m>0`$，近似律也给正质量，归一化的两分支后验满足 $`\operatorname{TV}\le\|p-\widetilde p\|_1/m`$：把未归一化差与质量差分别界以 $`\|p-\widetilde p\|_1`$ 即得。小质量的放大明确存在，零支不定义后验。$`\square`$

**命题 C-5.4（一阶盲空间与二阶递推）。** 同源继续空窗的 $`N_k=qS^kc`$ 满足


```math
N_{k+2}=4N_{k+1}+N_k,\qquad
R_{k+3}=17R_{k+2}+17R_{k+1}-R_k,\quad R_k=\mathbb{\text{𝔼}}N_k^2.
```


全部一阶均值只看到 $`U=X+Y,V=Y+Z`$。在五态归一化仿射空间中，其盲空间是


```math
\operatorname{span}\{d,(1,-1,-1,1,0)^{\mathsf{\text{𝖳}}}\},
```


内部维数二；固定三个均值的纤维才是一维。

**证明。** $`S^2=4S+I`$ 给第一式。在列二次坐标 $`f(c)=(a^2,ab,b^2)^{\mathsf{\text{𝖳}}}`$ 上，$`f(Mc)=B_2f(c)`$，


```math
B_2=\begin{pmatrix}0&0&1\\0&1&1\\1&2&1\end{pmatrix},\qquad
B_2^3=\begin{pmatrix}1&4&4\\2&7&6\\4&12&9\end{pmatrix}.
```


直接相乘有 $`(B_2^3)^3-17(B_2^3)^2-17B_2^3+I=0`$，对平方响应线性评价后取期望得第二式。首两个一阶均值恰恢复 $`U,V`$，评价矩阵 $`(1,\xi,\eta)`$ 秩三；两个所列独立核向量因此生成归一化盲空间，边界须与非负单纯形相交。该结论针对无条件一阶空后缀序列，不抹掉同源已取得档案后的条件响应。每步独立重抽初始模式可能给相同各时刻边缘矩，却不是相同轨迹律。均匀初始律同源有 $`\Pr(N_1=29\mid N_0\ge5)=1/2`$，独立重抽版本为 $`1/5`$：前者条件只剩 $`3,13`$，后者 $`N_1`$ 与该档案独立。$`\square`$

## 6. 体积遗漏的符号如何进入同一原生未来

**约定 C-6.1（粗档案后的真实继续）。** 使用 [A 卷 §14](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#14-因子读口精确均值与原生条件守卫) 命题A-14.4的同状态奇偶档案与后缀 $`[5]`$ 回复表。观察者只保留实际首次回复奇偶 $`e`$，读者内部仍保留真实 $`(s,C)`$；不向粗档案免费加入精确数量、模式或接缝。以下体积桥消费同一条件律，不切换样本或阶段。

**命题 C-6.2（有符号残差与体积的任务连接）。** 置 $`m=Y+Z`$。$`m>0`$ 的实际奇数档案后，回复 $`(18,26,\bot)`$ 的条件律为


```math
\left(\frac Zm,\frac{Y-\kappa}m,\frac\kappa m\right).
```


$`r>0`$ 时实际拒绝率 $`g=\kappa/m`$、乘积补全预测 $`g_*=XY/(rm)`$ 满足


<table><tbody><tr><td>

```math
g-g_*=\frac\Delta{rm},\qquad
D=D_*-Zrm^2(g-g_*)^2,\quad
D_*=\frac ZrXY(r-X)(r-Y).
```

</td></tr></tbody></table>


给定内部精确 $`(X,Y,Z,D)`$，体积只确定误差绝对值；若两符号都落在合法纤维，恢复符号对于这项继续任务必要，一个二值补全标签充分。

**证明。** 表中两个接缝一分支拒绝，其余由 $`q(Sd_\sigma+d_3)`$ 得数量。奇数事件仅含 $`2,3,13`$，正质量 Bayes 给条件律。代入 $`\Delta`$ 和 §3 的 $`D`$ 得桥式。内部 $`Z,r,m`$ 正，二次式只能给 $`|\Delta|`$；固定均值后 $`\Delta`$ 的每一符号唯一确定 $`\kappa`$。中心点或只有一支合法不需要二值标签。此标签是给定精确模型数据的补全容量，不是从一个随机档案取得未知律的算法，也不是完整装置总成本一位。$`m=0`$ 时奇数档案不存在；$`r=0`$ 时唯一中间模式给确定十八，直接算而不除 $`r`$。$`\square`$

**命题 C-6.3（等体积、等四样本目标而未来不同）。** 两个已有来源律 [C-R3] 反例 11.10


```math
p^-=(1/10,3/10,1/5,3/10,1/10),\qquad
p^+=(3/10,1/10,1/5,1/10,3/10)
```


都有 $`X=Y=2/5,Z=1/5,m=3/5`$、协方差秩三、$`D=3/625`$。奇数档案后的条件回复却分别为


```math
(1/3,1/2,1/6),\qquad(1/3,1/6,1/2).
```


在各自另供的四 IID 合同内，完整平方体积律亦相同：$`\mathbb{\text{𝔼}}T=2/625`$，$`\Pr(T=1/36)=72/625`$、$`\Pr(T=0)=553/625`$。

**证明。** $`r=4/5,\Delta^\pm=\pm2/25`$，$`K=XY(r-X)(r-Y)=16/625,D_*=4/625`$，故 $`D=3/625`$。全概率正给秩三；由 §6.2 表得回复。四样本分布由命题 C-3.6 得。两律不是完整协方差相同：$`C_{12}`$ 分别 $`-3/50,7/50`$；完整 $`C`$ 在固定均值下本已恢复 $`\kappa`$。所以 $`(X,Y,Z,\operatorname{rank}C,D,e)`$ 不是该未来的充分边界，四样本另供资源不能接成同一个隐藏样本的免费分支。$`\square`$

**命题 C-6.4（四矩被实际供应后的有限消费者）。** 从四矩恢复 $`p`$ 后，在正质量奇偶支用 $`p_\sigma\mathbf{\text{𝟏}}_{e(\sigma)=e}`$ 归一化并推送到该样本当前 $`(x(\sigma),d_\sigma)`$，即决定表中下一回复及拒绝后继。另一份明确的历史“初窗后追加空窗”接缝已为零，随后再追加空窗的回复是 $`(0,34,55,89,123)`$，或追加模式 $`3`$ 的回复是 $`(5,39,60,94,128)`$，均为成功支。这些协议不互相重置或挪用反事实档案。

**证明。** 初窗后空窗的组成是 $`Sd_\sigma`$，两种后继分别 $`S^2d_\sigma`$ 和 $`S^2d_\sigma+d_3`$，用 $`q`$ 算得表。以实际档案选定同一隐藏样本，再按其条件概率求和即得全部回复律。公开阶段、来源标识、资源和保留档案也是边界的一部分，数值 $`p`$ 须由合同供应或取得，不能由奇偶一项推断。菜单、守卫拒绝、吸收后继都按定义 C-1.3；零质量档案无后验。$`\square`$

## 7. 活动来源的端点消元与模型内反演

前述残差与四矩适用于声明的五态律。现在收紧来源为正活动权模型，检验何时端点读出足以反演被合并的中位，并把反演实际送入同一守卫回复。

### 7.1 三个位、两个排斥与五种模式

**定义 C-7.1（活动来源）。** 采用 [A 卷 §1](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#1-有序原子五种选择与标准窗口) 的统一五模式和位序字典；$`a,b,c`$ 分别是低、中、高位置的实活动权。它们是来源权重，分别区别于原生数量 $`0,2,3,5,7`$、组成和几何面积。

声明 $`a,b,c>0`$；按每个被选位置计一次活动权，恰有


<table><tbody><tr><td>

```math
\mathcal{\text{𝒵}}=(1+a)(1+c)+b,\qquad
p=(p_0,p_1,p_2,p_3,p_{13})
=\frac{(1,a,b,c,ac)}{\mathcal{\text{𝒵}}}.
```

</td></tr></tbody></table>


**证明。** 中位未选时，两端四配置给权 $`1,a,c,ac`$；中位被选时，两端必须为零，给权 $`b`$。五项和为 $`\mathcal{\text{𝒵}}>0`$，除以它即为归一化律。空配置权一与数量零相容。$`\square`$

这是既有正活动权五模式模型的明确实例，满足底面乘法约束 $`p_0p_{13}=p_1p_3`$。[^CE-D] 合法语法只限定支撑，不指定这些概率；任意五模式律可以违反此约束。多窗采用活动权乘法，还必须另行声明完整路径的因子化来源。

加权独立集的硬核模型定义是此来源的成熟背景：Sinclair、Srivastava、Yin 的版本 v2 §1.1 使用统一活动 $`\lambda>0`$ 和权 $`\lambda^{|I|}`$。[^CE-HC] 本文逐点声明非齐次有限活动并直接证明公式；该文具有活动阈值和图族条件的强空间混合定理不承担这里任意正权路径的恒等式。

### 7.2 消去实际中位后的两端核

**定义 C-7.2（实际端点核）。** 以实际 $`x`$ 为行、实际 $`y`$ 为列，行列都按 $`0,1`$ 排序，定义


<table><tbody><tr><td>

```math
W(x,y)=\sum_{z=0}^1a^xb^zc^y
\mathbf{\text{𝟏}}_{\{xz=zy=0\}},\qquad
W=\begin{pmatrix}1+b&c\\a&ac\end{pmatrix},\qquad
P=\frac W{\mathcal{\text{𝒵}}}.
```

</td></tr></tbody></table>


只有 $`00`$ 格允许两个中位取值，故 $`W_{00}=1+b`$；其他三格都强制 $`z=0`$，权分别为 $`c,a,ac`$。因此 $`P_{00}=p_0+p_2`$，它合并空模式和中位模式，而没有把中位从来源中删除。

**定理 C-7.3（端点关联）。** 在定义 C-7.1 的来源内，


<table><tbody><tr><td>

```math
\det W=abc>0,\qquad
\operatorname{Cov}(x,y)=\det P=\frac{abc}{\mathcal{\text{𝒵}}^2}>0.
```

</td></tr></tbody></table>


**证明。** $`\det W=(1+b)ac-ca=abc`$。对任意非负归一化二元表，


```math
\begin{aligned}
\operatorname{Cov}(x,y)
&=P_{11}-(P_{10}+P_{11})(P_{01}+P_{11})\\
&=P_{00}P_{11}-P_{01}P_{10}=\det P,
\end{aligned}
```


其中用了四格和为一。矩阵全部除以 $`\mathcal{\text{𝒵}}`$，行列式除以 $`\mathcal{\text{𝒵}}^2`$。$`\square`$

此公式接到同一五模式的共同底面余量，而不是把两个不同的行列式合并。对一般 $`p`$，写


```math
P_{\mathrm{base}}=
\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix},
\quad
\Delta_{\mathrm{base}}=\det P_{\mathrm{base}},
\quad
X=\mathbb{\text{𝔼}} x,\ Y=\mathbb{\text{𝔼}} y,\ Z=\mathbb{\text{𝔼}} z,\ 
r=1-Z,\ \kappa=p_{13}.
```


这里 $`Z`$ 是中位均值，$`\mathcal{\text{𝒵}}`$ 才是配分总权。逐格合并中位得


<table><tbody><tr><td>

```math
\delta:=\det P
=\Delta_{\mathrm{base}}+Z\kappa
=\kappa-XY,\qquad
\Delta_{\mathrm{base}}=r\kappa-XY.
```

</td></tr></tbody></table>


若 $`r>0`$，§3 的共同底面残差命题给 $`\langle u,v\rangle=\Delta/r`$ 和底面条件协方差 $`\Delta/r^2`$。这里 $`\Delta_{\mathrm{base}}=\Delta`$。活动来源的 $`\Delta=0`$，但总体端点 $`\delta=Z\kappa>0`$；条件余量零不使总体两端独立。所用概率空间、实际共同底面与总体协方差仍取同一律。[^CE-D]

**操作区别。** 本来源的两种实际条件律为


```math
\Pr(x,y\mid z=0)=
\frac{a^xc^y}{(1+a)(1+c)},\qquad
\Pr(x=y=0\mid z=1)=1.
```


第一律是独立端点乘积，第二律确定端点全零。对 $`z`$ 求和是按 $`\Pr(z=0)=((1+a)(1+c))/\mathcal{\text{𝒵}}`$ 和 $`\Pr(z=1)=b/\mathcal{\text{𝒵}}`$ 混合两律，得到 $`P`$。真正删除中位及两条排斥因子，则重新定义二位来源，权仅为 $`a^xc^y`$，也得到上述独立端点律。条件 $`z=0`$ 与删除在这个特定模型中产生相同端点分布，但所用来源和操作不同：


<table><tbody><tr><td>

```math
\text{固定中位结果}\ne
\text{累计中位可能}\ne\text{删除中位及关系}.
```

</td></tr></tbody></table>


正协方差是同一来源约束的统计结果；它不额外定义两端之间的物理作用。

### 7.3 严格正端点表的逆像与同状态原生接续

**定理 C-7.4（完整正像与唯一逆）。** 设 $`P`$ 是实、严格正、四格和为一的 $`2\times2`$ 表。它来自定义 C-7.1 的 $`a,b,c>0`$ 模型，当且仅当 $`\delta=\det P>0`$。此时参数和全部五质量唯一为


<table><tbody><tr><td>

```math
a=\frac{P_{11}}{P_{01}},\quad
c=\frac{P_{11}}{P_{10}},\quad
b=\frac{\delta}{P_{01}P_{10}}
=\frac{P_{00}P_{11}}{P_{01}P_{10}}-1,
```

</td></tr></tbody></table>


<table><tbody><tr><td>

```math

p=\left(
\frac{P_{01}P_{10}}{P_{11}},\
P_{10},\
\frac{\delta}{P_{11}},\
P_{01},\
P_{11}\right),\qquad
\mathcal{\text{𝒵}}=\frac{P_{11}}{P_{01}P_{10}}.

```

</td></tr></tbody></table>


特别地，恢复的中位概率是


<table><tbody><tr><td>

```math
p_2=\Pr(z=1)=\frac{\det P}{P_{11}}.
```

</td></tr></tbody></table>


**证明。** 模型中 $`P_{01}=c/\mathcal{\text{𝒵}},\ P_{10}=a/\mathcal{\text{𝒵}},\ P_{11}=ac/\mathcal{\text{𝒵}}`$，直接相除得到 $`a,c`$；定理 C-7.3 给 $`b`$ 与 $`p_2`$。这证明必要性和参数唯一性。

反向令 $`\rho=P_{01}P_{10}/P_{11}>0`$。因为
$`\delta/P_{11}=P_{00}-\rho`$，显示的五质量和为一，并且在 $`\delta>0`$ 时全部严格正。它们满足
$`\rho P_{11}=P_{10}P_{01}`$；除以 $`\rho`$ 得到 $`(1,a,b,c,ac)`$，总和为 $`1/\rho`$，重新归一化正好恢复给定 $`P`$。这证明充分性。$`\square`$

**边界。** 在仍然四格严格正的表中，$`\delta=0`$ 恰对应扩展模型的 $`b=0,\ a,c>0,\ p_2=0`$；它是 $`b>0`$ 来源的闭包边界，不属于严格正活动域。$`\delta<0`$ 无非负 $`b`$ 表示。含零格的端点表不进入这些正比值坐标；不得对 $`0/0`$ 任意赋值。一般五模式边界可直接用非负质量和求和定义处理。

**例 C-7.5（等五质量与不可识别的拆分）。**


```math
P=\frac15\begin{pmatrix}2&1\\1&1\end{pmatrix},
\quad \delta=\frac1{25},\quad
a=b=c=1,\quadp_2=\frac15.
```


然而任意五模式来源在此端点表上的全部逆像为


<table><tbody><tr><td>

```math
p(t)=(P_{00}-t,P_{10},t,P_{01},P_{11}),
\qquad 0\le t\le P_{00}.
```

</td></tr></tbody></table>


证明是前三个非 $`00`$ 格各自对应一个模式，$`00`$ 格只限制 $`p_0+p_2=P_{00}`$。底面乘法式进一步要求
$`(P_{00}-t)P_{11}=P_{10}P_{01}`$，才唯一给 $`t=\delta/P_{11}`$。上述表既容许五质量全为 $`1/5`$，也容许
$`(1/10,1/5,3/10,1/5,1/5)`$；后者中位质量 $`3/10`$，违反底面乘法式。

这个读出是固定的经典端点通道。若端点输出次序为 $`(00,10,01,11)`$，其矩阵为


```math
R_{\mathrm{end}}=
\begin{pmatrix}
1&0&1&0&0\\
0&1&0&0&0\\
0&0&0&1&0\\
0&0&0&0&1
\end{pmatrix}.
```


它在归一化切空间中的遗忘方向是 $`(1,0,-1,0,0)`$。这与保留三均值时的仿射回路
$`(1,-1,0,-1,1)`$ 不同：端点表保留 $`\kappa`$ 而忘掉空／中位拆分，三均值保留 $`Z`$ 而忘掉底面回路。来源模型约束使前一种遗忘在模型内可逆，不使一般未知律的信息损失消失。该区别接到完整律、固定读出与实际统计取得的分层。[^CE-F]

**同一来源的下一回复合同。** [A 卷 §16](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#16-同一有序前缀的接缝余数组成图) 定义A-16.1和 [A 卷 §14](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#14-因子读口精确均值与原生条件守卫) 命题A-14.4固定同一初始化读者、首回复及继续 $`[5]`$ 的逐源回复表。首次模式实际来自上述活动律；后缀在同一真实状态执行，拒绝仍吸收，档案后处理不改状态。这里直接把端点反演所得五质量送入此已证明接口。[^CE-G][^CE-F]

**命题 C-7.6（端点逆式消费于实际下一回复）。** 精确 $`P`$ 与活动来源条件另外作为模型数据供应时，定理 C-7.4 的逆式预测该实际继续回复的无条件律：


<table><tbody><tr><td>

```math

\bigl(\Pr(R=5),\Pr(R=18),\Pr(R=26),\Pr(R=\bot)\bigr)
=\left(
\frac{P_{01}P_{10}}{P_{11}},\
\frac{\delta}{P_{11}},\
P_{01},\
P_{10}+P_{11}\right).

```

</td></tr></tbody></table>


若观察者把已收到的首次精确数量后处理为奇偶，只保留实际奇数事件
$`A=\{Q_{\mathrm{nat}}\text{ 为奇数}\}=\{2,3,13\}`$，则


<table><tbody><tr><td>

```math
m=\Pr(A)=\frac{\delta}{P_{11}}+P_{01}+P_{11}>0,
\qquad
\Pr(R=(18,26,\bot)\mid A)
=\frac1m\left(\frac{\delta}{P_{11}},P_{01},P_{11}\right).
```

</td></tr></tbody></table>


**证明。** 将恢复的同一五质量代入逐源回复表即得无条件推前律。在 $`A`$ 内只剩中位、高位和两端模式，质量为 $`p_2,p_3,p_{13}`$，除以它们同一个正和 $`m`$ 得条件律。读者自身仍保留真实接缝和组成，归档粗化不改变其更新。拒绝支质量保留。$`\square`$

另一种明确的档案后处理，是由首次精确回复查表后仅保留 $`(x,y)`$。在实际 $`00`$ 记录下，


<table><tbody><tr><td>

```math
\Pr(R=18\mid00)=\frac{\delta}{P_{00}P_{11}}
=\frac b{1+b},\qquad
\Pr(R=5\mid00)=\frac1{1+b}.
```

</td></tr></tbody></table>


$`01`$ 记录下回复确定为 $`26`$；$`10`$ 或 $`11`$ 下确定拒绝。证明是 $`00`$ 后验仅含 $`p_0/P_{00},p_2/P_{00}`$ 两支，二者接缝均零但组成不同。例 C-7.5 中模型预测 $`18`$ 的条件概率为 $`1/2`$；同端点表的非乘法来源 $`p_2=3/10`$ 给 $`3/4`$。

这些是实际首次回复的确定后处理，不是额外免费端点仪器。首次精确 $`Q_{\mathrm{nat}}\in\{0,2,3,5,7\}`$ 本来就识别该次模式；粗档案主动丢弃其中区别。精确人口律与模型条件也不从一个回复或有限样本自动取得。可计算经验律不等于认证真实参数；没有另供抽样合同，不把相关历史当作 IID 样本。任务止于这一继续回复，没有复制、重抽、重置或新原生停止动作。

### 7.4 消元留下的完整对数四角项

**定义 C-7.7（有效四角系数）。** 对严格正四格 $`W`$ 使用自然对数：


<table><tbody><tr><td>

```math
J_{\mathrm{eff}}
=\log W_{00}+\log W_{11}-\log W_{01}-\log W_{10}
=\log(1+b).
```

</td></tr></tbody></table>


交叉比为 $`(1+b)ac/(ca)=1+b`$，所以该系数只取决于中位活动 $`b`$。

**定理 C-7.8（完整且唯一的双线性表示）。**


<table><tbody><tr><td>

```math
\begin{aligned}
\log W(x,y)
={}&\log(1+b)
+x\log\frac a{1+b}
+y\log\frac c{1+b}
+xy\log(1+b).
\end{aligned}
```

</td></tr></tbody></table>


**证明。** 在 $`00,10,01,11`$ 依次评价得到
$`\log(1+b),\log a,\log c,\log(ac)`$。一般表示 $`A_0+A_1x+A_2y+A_{12}xy`$ 的这四个评价依次确定四系数，因此表示唯一，$`A_{12}`$ 正是四角差。$`b>0`$ 使它非零，常数和两个单端项不能替代。归一化只把常数减去 $`\log\mathcal{\text{𝒵}}`$。$`\square`$

有限因子化模型中，把所有涉及同一待消变量的因子相乘，再对该变量求和，会在其存活邻居上产生新因子；这里该因子就是 $`W`$。这是 Peyrard 等版本 v2 §3.2 的 sum-product 消元步骤在本来源中的消费。[^CE-VE] 后面的星形也使用同一步骤。排斥零格允许非负势，不需借严格正势的图模型等价定理；取对数只用于已经严格正的边界因子。

本系数同时是命题 C-7.6 的实际预测参数：


<table><tbody><tr><td>

```math
\Pr(R=18\mid00)=1-\exp(-J_{\mathrm{eff}}).
```

</td></tr></tbody></table>


它描述隐藏模式分支的质量，不独立添加一个物理相互作用或可自由控制的参数。

### 7.5 实际端点与外接缝相差一条排斥边

**定义 C-7.9（兼容矩阵与两个读口）。** 以旧位为行、新位为列，定义


```math
Q_{\mathrm{ex}}=
\begin{pmatrix}1&1\\1&0\end{pmatrix},
\quad D(t)=\operatorname{diag}(1,t),\quad
B(t)=Q_{\mathrm{ex}}D(t)=\begin{pmatrix}1&t\\1&0\end{pmatrix}.
```


它只禁止 $`11`$；$`B(t)`$ 给新位活动一次。令
$`J_{\mathrm{swap}}=\begin{pmatrix}0&1\\1&0\end{pmatrix}`$，则
$`Q_{\mathrm{ex}}=J_{\mathrm{swap}}MJ_{\mathrm{swap}}`$。这是坐标矩阵恒等式；$`M`$ 推进组成或树替换，$`Q_{\mathrm{ex}}`$ 的指标却是实际占位兼容性。

**定理 C-7.10（额外边与反号）。** 辅助低到高核的行是窗口外低端输入接缝，列为实际高端 $`y`$；原生高到低核的行是窗口外高端输入接缝，列为实际低端 $`x`$。它们分别满足


<table><tbody><tr><td>

```math
\begin{aligned}
K_{\mathrm{low}}
&=B(a)B(b)B(c)=Q_{\mathrm{ex}}W
=\begin{pmatrix}1+a+b&c(1+a)\\1+b&c\end{pmatrix},\\
K_{\mathrm{high}}
&=B(c)B(b)B(a)=Q_{\mathrm{ex}}W^{\mathsf{\text{𝖳}}}
=\begin{pmatrix}1+c+b&a(1+c)\\1+b&a\end{pmatrix},\\
\det K_{\mathrm{low}}&=\det K_{\mathrm{high}}=-abc.
\end{aligned}
```

</td></tr></tbody></table>


**证明。** 低端外接缝 $`s`$ 必须与实际 $`x`$ 兼容，故核为
$`\sum_xQ_{\mathrm{ex}}(s,x)W(x,y)`$。高端外接缝则须与 $`y`$ 兼容，求和给
$`\sum_yQ_{\mathrm{ex}}(s,y)W(x,y)`$，即第二式。矩阵相乘得到各格；$`\det Q_{\mathrm{ex}}=-1`$ 使两行列式反号。每条核多含一个真实外接缝排斥连接。$`\square`$

这直接消费已声明的两个读向及其活动核。[^CE-C][^CE-F] 原生守卫是 $`s\,y=0`$、输出接缝是 $`x`$；辅助守卫是 $`s\,x=0`$、输出是 $`y`$。单位活动时矩阵数值相同，也不能互换原生在线合同。反转完整有限词还要反转窗口次序、各窗活动和外端条件；它不保持同步前缀回复。

同一归一化模式律给 $`K_{\mathrm{low}}/\mathcal{\text{𝒵}}=Q_{\mathrm{ex}}P`$ 和
$`K_{\mathrm{high}}/\mathcal{\text{𝒵}}=Q_{\mathrm{ex}}P^{\mathsf{\text{𝖳}}}`$。高读两行和为 $`1,1-Y`$，低读为 $`1,1-X`$；它们是绝对合法质量核，不是默认随机矩阵。若合同是同律提议，缺失质量就是拒绝；若合同要求通过后条件化，须保留正通过质量和条件事件。把各行各自归一化，不能替代已指定整链的整体归一化。

因此底面 $`\Delta_{\mathrm{base}}`$、端点 $`\delta`$、外接缝行列式有不同语义。在正活动源中前者为零、第二个为正、第三个为负；负行列式是有向响应翻转，所有概率仍非负。

## 8. 因子化长链、Fibonacci 关系与有限端点误差

单窗端点核可按共同内部索引组合，但行列式乘法要求完整路径的因子化权重。本节给精确传播、条件响应与端点近似误差，不将它们推广到一般数量未来。

### 8.1 正因子化路径的精确收缩与符号

**定义 C-8.1（完整路径来源）。** 设正整数 $`N`$，实际位
$`b_1,\ldots,b_N\in\{0,1\}`$，相邻满足 $`b_ib_{i+1}=0`$，实活动 $`w_i>0`$。另外声明完整配置权


```math
\omega(b)=\prod_{i=1}^Nw_i^{b_i},
\qquad
W_N(s,t)=
\sum_{\substack{b_1=s,\ b_N=t\\b_ib_{i+1}=0}}\omega(b).
```


这里没有额外内部耦合或固定外端，$`s,t`$ 是实际首尾位。取 $`D_i=\operatorname{diag}(1,w_i)`$。

**定理 C-8.2（指定端点的完整收缩）。** 对 $`N\ge2`$，


<table><tbody><tr><td>

```math
W_N=D_1Q_{\mathrm{ex}}D_2\cdots
Q_{\mathrm{ex}}D_N,\qquad
\det W_N=(-1)^{N-1}\prod_{i=1}^Nw_i.
```

</td></tr></tbody></table>


令 $`\mathcal{\text{𝒵}}_N=\sum_{s,t}W_N(s,t)>0,\ P_N=W_N/\mathcal{\text{𝒵}}_N`$，则


<table><tbody><tr><td>

```math
\operatorname{Cov}(b_1,b_N)
=\frac{(-1)^{N-1}\prod_iw_i}{\mathcal{\text{𝒵}}_N^2}.
```

</td></tr></tbody></table>


**证明。** 展开矩阵乘积的内部指标，每个指标就是一个实际位。每个 $`D_i`$ 给该位置活动一次，每个 $`Q_{\mathrm{ex}}`$ 给该相邻排斥一次；非零乘积项与合法位串权重保持一一对应。有限求和因此给 $`W_N`$。行列式乘法使用 $`\det D_i=w_i,\ \det Q_{\mathrm{ex}}=-1`$；再用定理 C-7.3 的任意二元表恒等式归一化。$`\square`$

相距奇数条排斥边的不同端点负相关，相距偶数条排斥边的不同端点正相关；正活动使相关非零。$`N=2`$ 的 $`11`$ 格为零，所以不能把第三、四节的严格正表比值和对数公式直接应用于所有链核。

**同位端点 $`N=1`$。** 两端名指同一个实际位，须定义


<table><tbody><tr><td>

```math
W_1(s,t)=\mathbf{\text{𝟏}}_{\{s=t\}}w_1^s
=\operatorname{diag}(1,w_1),\quad
\mathcal{\text{𝒵}}_1=1+w_1,\quad
\operatorname{Cov}(b_1,b_1)=\frac{w_1}{(1+w_1)^2}.
```

</td></tr></tbody></table>


证明是枚举同位联合的 $`00,11`$ 两配置。行列式仍为 $`w_1`$，但此协方差是方差，没有两个不同端点或真正切口。$`N=0`$ 没有端点任务，不作端点公式断言。

**开放接入与来源限制。** 对已声明的非负外端因子 $`\ell,r`$，完整加权响应为
$`\ell^{\mathsf{\text{𝖳}}}W_Nr`$。这是同一来源有限求和的重排；若总质量零，不产生条件概率。拼接块必须共享实际指标且各因子只计一次。若两个端点块都已包含同一共享位置的 $`D`$，不能直接相乘而重复计权；可把该因子只分配到一侧，或在明确重复处补偿。

这些是严格同源收缩的条件在当前路径中的实例。[^CE-G] 局部边缘相同、接缝合法都不强制完整来源采用 $`\omega(b)`$。例如只输入空／中位的合法双窗，令位 $`A,B`$ 的四质量为
$`(\theta,1/2-\theta,1/2-\theta,\theta)`$，$`0\le\theta\le1/2`$。局部各半且接缝恒零，同一原生终值却是 $`13A+3B`$：$`\theta=1/2`$ 给 $`\{0,16\}`$，$`\theta=0`$ 给 $`\{3,13\}`$，追加实际空窗分别给 $`\{0,68\}`$、$`\{13,55\}`$。[^CE-C] 这类共同历史与高阶相关源保留其真实联合律；不能用活动乘积的特殊补全覆盖它。

### 8.2 等权 Fibonacci 端点、概率尺度与模数

取 $`w_i=1`$，标准约定 $`F_0=0,\ F_1=1,\ F_{n+2}=F_{n+1}+F_n`$，只使用非负索引。

**定理 C-8.3（等权闭式）。** 对 $`N\ge2`$，


<table><tbody><tr><td>

```math
W_N=Q_{\mathrm{ex}}^{N-1}
=\begin{pmatrix}F_N&F_{N-1}\\F_{N-1}&F_{N-2}\end{pmatrix},
\quad\mathcal{\text{𝒵}}_N=F_{N+2},
\quad\operatorname{Cov}(b_1,b_N)
=\frac{(-1)^{N-1}}{F_{N+2}^2}.
```

</td></tr></tbody></table>


**证明。** $`N=2`$ 时矩阵为 $`Q_{\mathrm{ex}}`$，对应 $`F_2,F_1,F_0`$。假设某 $`N`$ 闭式成立，右乘 $`Q_{\mathrm{ex}}`$，四格成为
$`F_N+F_{N-1},F_N,F_{N-1}+F_{N-2},F_{N-1}`$，恰是 $`N+1`$ 的闭式。四格和为
$`F_N+2F_{N-1}+F_{N-2}=F_{N+2}`$，定理 C-8.2 给最后一式。$`\square`$

| 实际位置数 $`N`$ | 合法配置数 $`F_{N+2}`$ | 两端协方差 |
| ---: | ---: | --- |
| $`2`$ | $`3`$ | $`-1/9`$ |
| $`3`$ | $`5`$ | $`1/25`$ |
| $`4`$ | $`8`$ | $`-1/64`$ |
| $`5`$ | $`13`$ | $`1/169`$ |
| $`6`$ | $`21`$ | $`-1/441`$ |

$`N=3`$ 是等五模式来源；$`N=1`$ 则另有 $`W_1=I`$、配置数二、同位方差 $`1/4`$，不用 $`F_{-1}`$。

**实际原生全窗接口。** 对 $`L\ge1`$，把 $`N=3L`$ 个位按原生高、中、低的顺序分窗，初始外高接缝零、末低端自由。每个无 $`11`$ 位串唯一给一个合法原生窗口词，活动按该顺序给定；有序核积为


```math
\mathcal{\text{𝒵}}_{3L}
=(1,0)\left(\prod_{j=1}^L
K_{\mathrm{high},j}\right)\binom11 .
```


这里 $`w_{3j-2}=c_j,\ w_{3j-1}=b_j,\ w_{3j}=a_j`$。单位权时
$`K_{\mathrm{high}}=Q_{\mathrm{ex}}^3`$，所以开放历史数为 $`F_{3L+2}`$。这消费既有整窗计数，保持原生顺序，没有交换在线方向。[^CE-C]

**尺度与模数。** 两个未归一化响应列的坐标平行四边形面积为


<table><tbody><tr><td>

```math
\lvert\det W_N\rvert=1,\qquad
\lvert\det P_N\rvert=\frac1{F_{N+2}^2}.
```

</td></tr></tbody></table>


后一式同时缩放两列，故出现平方分母。这是响应坐标面积，不是实际空间面积；未归一化保持与概率归一化缩小各有自己的尺度。

整数核的行列式为单位 $`\pm1`$，整数伴随矩阵给逆。因此它在每个 $`\mathbb{\text{ℤ}}/m\mathbb{\text{ℤ}}`$、$`m\ge2`$ 中可逆；某个 Fibonacci 项模素数为零，不使整个核退化。归一化的 $`P_N`$ 要作为模对象，另须
$`\gcd(F_{N+2},m)=1`$。例如 $`N=4`$ 时
$`W_4=\begin{pmatrix}3&2\\2&1\end{pmatrix}`$ 模二是单位阵，而总权八模二非单位，概率式不能在此除以八。此整数核结论不运输到任意实活动，也不赋予逆原生动作或内部历史恢复。

### 8.3 右消息、黄金固定点与实际条件响应

**定义 C-8.4（右列消息坐标）。** 对非负核
$`H=\begin{pmatrix}A&B\\C&D\end{pmatrix}`$，取非零非负右消息 $`h`$，且 $`h_0>0`$，令 $`t=h_1/h_0\ge0`$。在 $`A+Bt>0`$ 时，左消息 $`Hh`$ 的一／零比例是


<table><tbody><tr><td>

```math
T_H(t)=\frac{C+Dt}{A+Bt},\qquad
T_H'(t)=\frac{\det H}{(A+Bt)^2}.
```

</td></tr></tbody></table>


**证明。** $`Hh=h_0(A+Bt,C+Dt)^{\mathsf{\text{𝖳}}}`$；商求导的分子为
$`D(A+Bt)-B(C+Dt)=AD-BC`$。$`\square`$

纯代数导数只需分母非零；概率消息比例须分母正。若 $`h_0=0`$，直接计算 $`Hh`$，不套有限 $`t`$ 坐标；若返回零分量为零，有限比值也未定义。此响应是外端权的收缩比例，不是默认随机转移或额外因果实验。

对单位排斥，


<table><tbody><tr><td>

```math
T_{Q_{\mathrm{ex}}}(t)=\frac1{1+t},\quad
\varphi=\frac{1+\sqrt5}{2},\quad
t_*=\varphi^{-1},\quad
T_{Q_{\mathrm{ex}}}'(t_*)=-\varphi^{-2}.
```

</td></tr></tbody></table>


固定点方程为 $`t^2+t-1=0`$，唯一正根 $`\varphi^{-1}`$，且 $`1+t_*=\varphi`$。消息复合满足 $`T_{H_1H_2}=T_{H_1}\circ T_{H_2}`$，在同一固定点用链式法则得到


<table><tbody><tr><td>

```math

(T_{Q_{\mathrm{ex}}^3})'(t_*)=-\varphi^{-6},
\qquad
(T_{W_3})'(t_*)=(T_{Q_{\mathrm{ex}}^2})'(t_*)
=+\varphi^{-4}.
```

</td></tr></tbody></table>


三次 $`Q_{\mathrm{ex}}`$ 是三位置外接缝核；三位置实际端点 $`W_3`$ 只有两条边。负号与局部偏差换边、倍率与局部衰减来自此固定点计算。它不提供所有 $`t\ge0`$ 的统一严格一步收缩，因为
$`|T_{Q_{\mathrm{ex}}}'(0)|=1`$；也不提供任意非单位活动链的黄金速率。

**命题 C-8.5（等权端点条件差）。** 对 $`N\ge2`$，


<table><tbody><tr><td>

```math
\Pr(b_N=1\mid b_1=1)-\Pr(b_N=1\mid b_1=0)
=\frac{(-1)^{N-1}}{F_NF_{N+1}}.
```

</td></tr></tbody></table>


**证明。** $`W_N`$ 的零行和为 $`F_{N+1}`$，一行和为 $`F_N`$，都正。对实际联合律的两行条件归一化，得到
$`W_{11}/F_N-W_{01}/F_{N+1}`$；通分分子等于
$`W_{00}W_{11}-W_{01}W_{10}=\det W_N`$，再用定理 C-8.2。$`N=2`$ 的一行 $`11`$ 格虽为零，条件事件仍正，差为 $`-1/2`$。$`\square`$

对原生 $`L`$ 窗，令 $`H_1=b_1`$ 是首个高位，$`G`$ 是在同一状态追加 $`[5]`$ 的拒绝指示。实际终端接缝是 $`b_N`$，故 $`G=b_N`$，$`N=3L`$。因此


<table><tbody><tr><td>

```math
\operatorname{Cov}(H_1,G)
=\frac{(-1)^{3L-1}}{F_{3L+2}^2},\quad
\Pr(G=1\mid H_1=1)-\Pr(G=1\mid H_1=0)
=\frac{(-1)^{3L-1}}{F_{3L}F_{3L+1}}.
```

</td></tr></tbody></table>


这是实际首位／下一守卫任务的条件比较；有条件均须有正条件质量。它不把条件化解释为对首位的因果干预，也不声称取得了后续所有数量回复的律。

### 8.4 有限端点任务的精确独立近似误差

**定义 C-8.6（同边缘独立补全）。** 对任意二元联合律 $`P`$，令
$`P^{\mathrm{ind}}(s,t)=P_L(s)P_R(t)`$，使用 $`P`$ 自己的两端边缘。总变差约定为
$`\operatorname{TV}(P,Q)=\frac12\sum_{s,t}|P(s,t)-Q(s,t)|`$。

**定理 C-8.7（精确端点误差）。** 写 $`\delta=\operatorname{Cov}(b_1,b_N)`$，则


<table><tbody><tr><td>

```math
P-P^{\mathrm{ind}}
=\delta\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\qquad
\operatorname{TV}(P,P^{\mathrm{ind}})=2|\delta|.
```

</td></tr></tbody></table>


特别对定义 C-8.1 的正活动链，


<table><tbody><tr><td>

```math
\operatorname{TV}(P_N,P_N^{\mathrm{ind}})
=\frac{2\prod_iw_i}{\mathcal{\text{𝒵}}_N^2};
\qquad w_i=1,\ N\ge2:\ 
\operatorname{TV}=\frac2{F_{N+2}^2}.
```

</td></tr></tbody></table>


**证明。** $`11`$ 格的差为 $`P_{11}-P_L(1)P_R(1)=\delta`$。差表的两行和、两列和都零，其他三格因此被强制为 $`-\delta,-\delta,\delta`$。半绝对和为 $`2|\delta|`$。代入定理 C-8.2–C-8.3。$`\square`$

对任何已指定端点目标 $`0\le f(s,t)\le1`$，


<table><tbody><tr><td>

```math
|\mathbb{\text{𝔼}}_Pf-\mathbb{\text{𝔼}}_{P^{\mathrm{ind}}}f|
\le\operatorname{TV}(P,P^{\mathrm{ind}}).
```

</td></tr></tbody></table>


证明是差表正质量总和等于负质量绝对值总和、均为 TV；对 $`f\in[0,1]`$ 积分介于负 TV 和正 TV。正差格的事件指示达到上界。若 $`\delta>0`$ 选 $`\{00,11\}`$，若 $`\delta<0`$ 选 $`\{01,10\}`$。已指定共同随机后处理也保持此界：把差表乘同一随机核，输出绝对和由三角不等式不增，但这不包括条件归一化的后选择。

**容差的整数条件。** Fibonacci 递推与 $`\varphi^2=\varphi+1`$ 给
$`F_{N+2}\ge\varphi^N`$：初始 $`N=0`$ 为 $`1=1`$、$`N=1`$ 为 $`2\ge\varphi`$；相邻两界相加即得下一界。因此对 $`\varepsilon>0`$、整数


<table><tbody><tr><td>

```math
N\ge
\max\left\{2,\
\left\lceil\frac{\log(2/\varepsilon)}{2\log\varphi}\right\rceil
\right\},
```

</td></tr></tbody></table>


单位链的上述端点误差不超过 $`\varepsilon`$。更锐利的精确判定为
$`F_{N+2}^2\ge2/\varepsilon`$；对数界是充分条件，不一定是最短长度。$`\varepsilon=0`$ 时没有有限 $`N\ge2`$ 达到独立。只接完整原生窗时选 $`N=3L`$；例如充分条件可写


```math
L\ge\max\left\{1,\
\left\lceil\frac{\log(2/\varepsilon)}{6\log\varphi}\right\rceil
\right\},
```


精确条件仍是 $`F_{3L+2}^2\ge2/\varepsilon`$。$`N=1`$ 另有同位联合
$`\operatorname{TV}=2w_1/(1+w_1)^2`$，单位活动时为 $`1/2`$。

**实际消费者和限制。** §8.3的 $`G=b_N`$ 使联合事件
$`\{H_1=1,G=1\}`$ 的独立补全误差恰为有符号 $`\delta`$；有界端点守卫目标都受此 TV 界控制。此结论保留同源的有限端点任务和容差，不含抽样、舍入或模型误设误差。非单位活动没有上述统一黄金界。

独立端点补全不自动构造合法整链。精确 $`W_N`$ 在每个有限正活动长度仍满秩；当前小误差也不恢复内位、控制稀有事件后验误差或保证所有未来数量与相干任务。后选择须使用实际正条件质量及其误差运输，不能沿用无条件 TV 数字。

**例 C-8.8（相同端点仍有不同的允许数量未来）。** 取原生高到低读序六位词
$`000000`$ 与 $`010000`$，即两窗口 $`([null],[null])`$ 与 $`([3],[null])`$。两者合法且首尾同为 $`00`$。同一初态递推给最终组成
$`C=(0,0)^{\mathsf{\text{𝖳}}}`$ 与 $`C=S(0,1)^{\mathsf{\text{𝖳}}}=(2,3)^{\mathsf{\text{𝖳}}}`$，终端接缝均零。再在各自实际状态追加 $`[5]`$，回复为
$`5`$ 与 $`q(S(2,3)^{\mathsf{\text{𝖳}}}+(1,1)^{\mathsf{\text{𝖳}}})=60`$。

所以端点表只对它收缩的任务充分；完整原生数量未来还需要组成边界或其正确条件律。当前占位 $`0/1`$ 不是组成坐标差。既有动态下降判据要求在固定动作、记录和资源合同下，观察、可用性、失败支及后继边界都在摘要纤维上恒定；仅保持一次端点观察不满足它。[^CE-G]

## 9. 共同记录的圆盘与参考递归

**假设 C-9.1（共同纯记录）。** 另供同一个复 Hilbert 载体、归一化记录 $`o,u_0,v_0`$ 及可取得的关系条目。内积共轭线性于第一槽、线性于第二槽。置 $`a=\langle o,u_0\rangle,b=\langle o,v_0\rangle,c=\langle u_0,v_0\rangle`$。已知 $`a,b`$、待补 $`c`$ 的 Gram 为


```math
G_{\rm rec}=\begin{pmatrix}1&a&b\\\bar a&1&c\\\bar b&\bar c&1\end{pmatrix}.
```


[C-R4] §109 的退相干记录矩阵 $`\Gamma_{ij}=\langle e_j,e_i\rangle`$ 是通常 Gram 的转置；正性和秩相同，密度非对角因子的索引约定仍须保持。

**命题 C-9.2（给定共同参考后的精确可实现性）。** 此三记录可在某个复 Hilbert 空间共同实现，当且仅当 $`|a|,|b|\le1`$ 且


<table><tbody><tr><td>

```math
|c-\bar a b|^2\le(1-|a|^2)(1-|b|^2).
```

</td></tr></tbody></table>


其行列式为右侧容量减左侧平方。两模长均小于一时，盘内秩三、圆周秩二；两模长均一时秩一；恰一个模长一时秩二。这里秩是该纯记录实现的最小载体维数。

**证明。** $`u_\perp=u_0-ao,v_\perp=v_0-bo`$ 的范数平方分别 $`A=1-|a|^2,B=1-|b|^2`$，内积 $`c-\bar a b`$，故必要性由 Cauchy–Schwarz。$`A>0`$ 时构造


```math
o=(1,0,0),\quad u_0=(a,\sqrt A,0),\quad
v_0=\left(b,\frac{c-\bar a b}{\sqrt A},
\sqrt{B-\frac{|c-\bar a b|^2}{A}}\right).
```


条件保证归一化和所有重叠；$`A=0`$ 时强制 $`c=\bar a b`$，取 $`u_0=ao,v_0=bo+\sqrt B f`$，$`f\perp o`$。消去参考列后 $`G_{\rm rec}`$ 合同于 $`1`$ 加二阶残差 Gram，给行列式和全部秩分支。任意记录的 Gram 秩等于其张成维数，谱平方根实现达到该维数，故最小性成立；固定 $`\mathbb{\text{ℂ}}^2`$ 载体只允许秩至多二，不能实现任意盘内点。$`\square`$

**命题 C-9.3（成对合法但整体不合法）。** $`a=b=9/10,c=-9/10`$ 每对单位记录都可实现，但三者共同不可实现。

**证明。** 圆心 $`81/100`$、半径 $`19/100`$，实轴可行区间 $`[31/50,1]`$ 排除 $`-9/10`$。等价地 [C-R4] 命题 109.3 的矩阵在 $`(-1,1,1)`$ 上有特征值 $`-4/5`$，其余二值 $`19/10`$，行列式 $`-361/125`$。三个独立的成对实现不构成共同实现。$`\square`$

**定义 C-9.4（已经保留的参考列）。** 在同一载体中，$`E`$ 是满列秩参考列，$`F`$ 是待比较列，置 $`A=E^\dagger E>0,B=E^\dagger F,C=F^\dagger F`$。为避免与原生 $`S`$ 混淆，剩余关系记 $`\mathscr{\text{𝒮}}=C-B^\dagger A^{-1}B`$。

**命题 C-9.5（残差递归服务共同实现任务；Schur 中间步骤见 [C-L1] 附录 A.5.5）。**


<table><tbody><tr><td>

```math
P_E=E(E^\dagger E)^{-1}E^\dagger,\qquad
\mathscr{\text{𝒮}}=F^\dagger(I-P_E)F\succeq0,
```

</td></tr></tbody></table>


```math
\det\begin{pmatrix}A&B\\B^\dagger&C\end{pmatrix}
=\det A\det\mathscr{\text{𝒮}},\qquad
\operatorname{rank}G=\operatorname{rank}A+\operatorname{rank}\mathscr{\text{𝒮}}.
```


正主元 $`\mathscr{\text{𝒮}}_{aa}>0`$ 新增参考后剩余条目为


<table><tbody><tr><td>

```math
\mathscr{\text{𝒮}}'_{ij}=\mathscr{\text{𝒮}}_{ij}-
\frac{\mathscr{\text{𝒮}}_{ia}\mathscr{\text{𝒮}}_{aj}}{\mathscr{\text{𝒮}}_{aa}}.
```

</td></tr></tbody></table>


零主元强制整行整列零，不能除零。相关参考先取实际张成空间独立基；若用 $`A^+`$，须保留 $`\operatorname{range}B\subseteq\operatorname{range}A`$。

**证明。** $`P_E`$ 是正交投影，代入得残差 Gram。令


```math
W=\begin{pmatrix}I&-A^{-1}B\\0&I\end{pmatrix},\quad
W^\dagger G W=\begin{pmatrix}A&0\\0&\mathscr{\text{𝒮}}\end{pmatrix},\quad\det W=1,
```


证明行列式和秩；将一个剩余列分量投影到新参考给主元更新。PSD 的二阶主子式强制 $`|\mathscr{\text{𝒮}}_{ia}|^2\le\mathscr{\text{𝒮}}_{ii}\mathscr{\text{𝒮}}_{aa}`$，零主元遂行列全零。奇异参考的 PSD 候选若 $`v\in\ker A`$，对 $`(tv,w)`$ 的二次式任意变 $`t`$ 强制 $`v^\dagger Bw=0`$，即 $`(I-AA^+)B=0`$；在实际非零参考空间消元给 $`C-B^\dagger A^+B\succeq0`$ 及秩相加。全部大矩阵含冗余列时行列式零，不滥用非零行列式积。概率残差代入 $`E=b,F=(x,y),A=r`$；记录圆盘代入 $`E=o,F=(u_0,v_0),A=1`$。两者同为扣除共享投影，但布尔 Fréchet 区间与复记录圆盘的可行集不同；残差正性不替代事件非负性，代数条目可计算也不等于实际已取得。$`\square`$

**命题 C-9.6（三份共同记录的循环判据）。** 对同一单位记录 $`e_1,e_2,e_3`$，按第二槽线性的约定置 $`a=\langle e_1,e_2\rangle,b=\langle e_2,e_3\rangle,c=\langle e_3,e_1\rangle`$。共同实现当且仅当


```math
G=\begin{pmatrix}1&a&\bar c\\\bar a&1&b\\c&\bar b&1\end{pmatrix}
\text{ Hermitian},\quad |a|,|b|,|c|\le1,\quad
\det G=1-|a|^2-|b|^2-|c|^2+2\operatorname{Re}(abc)\ge0.
```


预定载体维数 $`d`$ 时还须 $`\operatorname{rank}G\le d`$；最小抽象载体维数等于此秩。

**证明。** 将共同参考取为 $`e_1`$，命题C-7.2中的三个条目依次为 $`a,\bar c,b`$，其精确圆盘不等式展开就是行列式非负；连同模界给必要性和充分构造。任意共同实现的 $`v^\dagger Gv=\|\sum_i v_i e_i\|^2`$ 非负；反向谱平方根 $`G=E^\dagger E`$ 的列归一化并实现全部重叠，实际张成维数等于 Gram 秩。因此分别合法的对子不能替代共同来源。所用单位、二阶主子式与秩条件都须保留。[C-R4] §§68、109；经典 Gram 工具同时供算术记录与几何记录分类消费。$`\square`$

**命题 C-9.7（成对模长遗漏闭环相位）。** 若三个重叠模长都为 $`1/\sqrt2`$，则 $`abc\ne0`$ 且共同实现要求 $`\cos\arg(abc)\ge1/\sqrt2`$。另供二维共同记录


```math
e_1=|0\rangle,\quad e_2=(|0\rangle+|1\rangle)/\sqrt2,\quad
 e_3^\pm=(|0\rangle\pm i|1\rangle)/\sqrt2
```


时三个成对模平方都为 $`1/2`$，但 $`abc=(1\pm i)/4`$，行列式为零。

**证明。** 代入命题C-7.6给 $`-1/2+(1/\sqrt2)\cos\arg(abc)\ge0`$。例中 $`a=c=1/\sqrt2,b=(1\pm i)/2`$；直接取内积和相乘给全部结论。独立重相位在环积中抵消，故成对模长遗忘的闭环关系并非标架更名可补。取得这些条目、比较相位及共同相干实现仍须另供；经典 $`\kappa`$ 与复环积也不是同一读口。$`\square`$

## 10. 闭路恢复须保留内部接缝权重

**定义 C-10.1（记录闭路；[C-L3] 式 (1)）。** 对同一归一化记录族 $`e_0,\ldots,e_{m-1}`$，令 $`g_{ij}=\langle e_i,e_j\rangle`$，


```math
B_{ijk}=g_{ij}g_{jk}g_{ki},\qquad
B_{0\cdots m-1}=g_{01}g_{12}\cdots g_{m-1,0}.
```


它们是 Bargmann 关系不变量，区别于二部振幅表的四角相位。

**命题 C-10.2（指定扇形恢复的完整域）。** 对 $`m\ge3`$，空乘积取一，有


<table><tbody><tr><td>

```math
\prod_{j=1}^{m-2}B_{0,j,j+1}
=B_{0\cdots m-1}\prod_{j=2}^{m-2}|g_{0j}|^2.
```

</td></tr></tbody></table>


全部内部接缝非零时可除以右侧权重恢复外圈；外圈亦非零时才能取辐角并相加模 $`2\pi`$。

**证明。** 独立重相位 $`e_i\mapsto e^{i\theta_i}e_i`$ 在每闭路逐点抵消，得规范不变性。展开扇形三角积，每条外圈边一次，每条内部对角线正反各一次，乘出 $`g_{0j}g_{j0}=|g_{0j}|^2`$。无除法恒等式在零接缝仍成立；恢复式与相位式分别需要上述非零条件。几何有向内部边可抵消，记录重叠权重不能一起删掉。引用 [C-L3] 的受控循环测量背景不意味着本模型已经供应它；实际取得三角和接缝条目须是同一载体的允许实验。$`\square`$

**命题 C-10.3（一个扇形失效而另一扇形可恢复）。** 取


```math
e_0=|0\rangle,\quad e_1=(|0\rangle+|1\rangle)/\sqrt2,\quad
e_2=|1\rangle,\quad e_3=(|0\rangle+i|1\rangle)/\sqrt2.
```


则 $`B_{012}=B_{023}=0`$，但 $`B_{0123}=i/4`$。替代接缝 $`13`$ 有


```math
B_{013}=B_{123}=(1+i)/4,\quad |g_{13}|^2=1/2,\quad
B_{0123}=B_{013}B_{123}/|g_{13}|^2=i/4.
```


**证明。** $`g_{02}=0`$ 使首两三角零。外圈重叠为 $`1/\sqrt2,1/\sqrt2,i/\sqrt2,1/\sqrt2`$，乘积 $`i/4`$；$`g_{13}=(1+i)/2`$，直接乘各三角得到所列数值。此例只证明这条替代接缝有效，未证明任意记录族总存在可恢复的剖分。改变坐标不产生遗漏条目，必须实际取得替代实验。$`\square`$

## 11. 原树中心符号与同源协方差运输

**约定 C-11.1（额外 Pauli 来源表示）。** 使用 [A 卷 §21](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#21-谱及-fourier-表示与真正相干来源的边界) 定义A-21.5的共同 $`\mathbb{\text{ℂ}}^2`$、$`a=-i\sigma_x,b=-i\sigma_y`$、右因子先作用的树表示及 $`L(\bar c)=b^va^u`$，$`u,v`$ 取模二类的 $`0,1`$ 整数代表。原拥有者为 [C-R4] §§101–108。另将空模式贡献声明为 $`I`$ 时，这只是该表示取值；原生空窗仍推进 $`C\mapsto SC`$，自由原树文法没有空树。

**命题 C-11.2（完整余循环与实面积的不同读口）。**


<table><tbody><tr><td>

```math
L(\bar c)L(\bar c')=(-1)^{\varepsilon(\bar c,\bar c')}L(\bar c+\bar c'),
\quad\varepsilon=uu'+vv'+uv'\pmod2.
```

</td></tr></tbody></table>


交换符号为 $`(-1)^{\det(\bar c,\bar c')}`$，$`\varepsilon`$ 满足二余循环恒等式且 $`\varepsilon(M\bar c,M\bar c')=\varepsilon(\bar c,\bar c')`$。实组成行列式经 $`M`$ 反号，奇偶不变。

**证明。** [A 卷 §21](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#21-谱及-fourier-表示与真正相干来源的边界) 命题A-21.6证明完整平方进位项 $`uu'+vv'`$、交换项 $`uv'`$ 和 $`M`$ 不变性。交换两个次序的指数和为 $`uv'+u'v=\det(\bar c,\bar c')`$ 模二；双线性给


```math
\varepsilon(x,y)+\varepsilon(x+y,z)=\varepsilon(y,z)+\varepsilon(x,y+z).
```


实行列式 $`\mathfrak{\text{𝔞}}(c,c')=\det(c,c')`$ 的双线性也给


```math
\mathfrak{\text{𝔞}}(c,c')+\mathfrak{\text{𝔞}}(c+c',c'')
=\mathfrak{\text{𝔞}}(c',c'')+\mathfrak{\text{𝔞}}(c,c'+c'').
```


这条无模二接缝式与余循环式分别保留各自的取值域。$`\det M=-1`$ 给实反号，模二下负号等于正号。全树表示保留一个中心位 $`s_t`$：$`U_t=(-1)^{s_t}L(c(t)\bmod2)`$。整数规范幂 $`b^Ba^A`$ 另有平方符号 $`(-1)^{\lfloor A/2\rfloor+\lfloor B/2\rfloor}`$；实际叶序再加每一 $`\alpha`$ 位于 $`\beta`$ 前的交换对数。故 $`(2,0)`$ 的 $`a^2=-I`$ 不能约化后删除中心位而当作 $`L(0,0)=I`$。两叶替换 $`a\mapsto b,b\mapsto ba`$ 与模二 $`M`$ 一致且中心位零，结构归纳和余循环不变给全树同步 $`\rho`$ 保持中心位。连续实面积的奇偶未定义，本式只对整数／二值组成，亦不供应量子测量。$`\square`$

**接口 C-11.3（同组成的持续相对符号）。** [A 卷 §21](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#21-谱及-fourier-表示与真正相干来源的边界) 命题A-21.6的两树 $`t_L,t_R`$ 同组成 $`(2,1)`$，酉分别 $`-b,b`$，且同步任意 $`\rho^n`$ 后仍相差负号；原语重相位在两来源乘相同标量，完整普通证明在那里给出。矩阵结合性遗忘括号，叶序不同仍保留；此符号不是§13新五态振幅比的自动赋值。$`\operatorname{Ad}_U=\operatorname{Ad}_{-U}`$，实际共同控制比较和环境条件必须另供，原拥有者 [C-R4] §107 的黑盒边界仍适用。

**命题 C-11.4（确定同步运输保留组成波动面积）。** 对同一来源律上的二维整数组成随机向量 $`c`$，假设有限二阶矩，确定推送 $`c\mapsto Mc`$。则


```math
\Sigma'=M\Sigma M^{\mathsf{\text{𝖳}}},\quad \det\Sigma'=\det\Sigma,
\qquad\Sigma=\operatorname{Cov}c.
```


协方差椭圆定义为 $`\Sigma^{1/2}`$ 作用于单位圆盘的像，面积 $`\pi\sqrt{\det\Sigma}`$；奇异时退化为线段或点、面积零。

**证明。** 线性映射与中心化交换，取期望得合同式；行列式乘 $`(\det M)^2=1`$。平方根像的二维面积缩放为其行列式，给椭圆式，无高斯假设。该任务不重抽、不重新加权、不删除测量记录。二维组成协方差、三维占位协方差和原树顺序是三份不同边界。$`\square`$

## 12. 底面相干实现：概率完整仍未决定乘积态

**假设 C-12.1（另供纯底面双量子位）。** $`r>0`$，在条件 $`z=0`$ 下真实供应归一化纯态，其系数矩阵为


```math
\mathcal{\text{𝒜}}=\frac1{\sqrt r}\begin{pmatrix}
\sqrt{p_0}e^{i\theta_0}&\sqrt{p_3}e^{i\theta_3}\\
\sqrt{p_1}e^{i\theta_1}&\sqrt{p_{13}}e^{i\theta_{13}}
\end{pmatrix}.
```


行、列是两个端点的 $`0,1`$ 标签。此条件模型不供应顶点与底面的相干，也不等于原树酉表示。四底角正时定义 $`\Phi=\theta_0+\theta_{13}-\theta_1-\theta_3\pmod{2\pi}`$。

**命题 C-12.2（相位与概率不匹配共同决定纯态任务）。** 局部行列重相位 $`\theta_{ij}\mapsto\theta_{ij}+\alpha_i+\beta_j`$ 保持 $`\Phi`$。该純态为乘积态当且仅当 $`\det\mathcal{\text{𝒜}}=0`$；正底面时等价于 $`\Delta=0`$ 且 $`\Phi=0`$。其纯态 concurrence 为 $`2|\det\mathcal{\text{𝒜}}|`$，并有


<table><tbody><tr><td>

```math
r^2|\det\mathcal{\text{𝒜}}|^2=
(\sqrt{p_0p_{13}}-\sqrt{p_1p_3})^2+
4\sqrt{p_0p_1p_3p_{13}}\sin^2(\Phi/2).
```

</td></tr></tbody></table>


**证明。** 四个行列相位在交替和中消去。二部纯态可分恰为非零系数矩阵秩一，即行列式零。令复对角乘积 $`l=c_0c_{13},h=c_1c_3`$，展开 $`|l-h|^2`$ 给所列式；四底角正时两项分别非负，第一项零等价于 $`p_0p_{13}=p_1p_3`$，第二项零等价于 $`\Phi=0`$。若有零振幅，直接用 $`|l-h|^2`$，不定义 $`\arg0`$；不完整 $`K_{2,2}`$ 支撑是森林，沒有四边相位循环。标准 concurrence 的纯态中间式 [C-L4] 式 (7) 是 $`|\langle\psi|\widetilde\psi\rangle|`$，将 $`\widetilde\psi=(\sigma_y\otimes\sigma_y)\overline\psi`$ 代入，内积绝对值为 $`2|\det\mathcal{\text{𝒜}}|`$。此使用不扩展到未知混态公式。$`\square`$

**命题 C-12.3（同经典律的乘积与最大纠缠见证）。** 五态均匀律条件底面四概率均 $`1/4`$。可以供应


```math
|\psi_0\rangle=(|00\rangle+|01\rangle+|10\rangle+|11\rangle)/2
=|+\rangle|+\rangle,
```


或 $`|\psi_\pi\rangle=(|00\rangle+|01\rangle+|10\rangle-|11\rangle)/2`$。后者 concurrence 一、两个约化态都是 $`I/2`$，前者零。

**证明。** 前者系数外积；后者系数矩阵 $`\frac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}`$ 与其伴随乘积为 $`I/2`$，行列式 $`-1/2`$。实际供应的 $`U_\phi=I+(e^{i\phi}-1)|11\rangle\langle11|`$ 可改变该闭路相位而不改占位概率；没有该资源不声称能操作它。经典对角混合 $`\sum(p_{ij}/r)|i\rangle\langle i|\otimes|j\rangle\langle j|`$ 始终可分，所以同概率不证明相干或纠缠。$`\square`$

## 13. 固定均值的五态相位商与复关系坐标

**假设 C-13.1（五维纯模式载体及标架）。** 另供正交模式基上的归一化 $`|\psi\rangle=\sum c_s|s\rangle`$，$`c_s=\sqrt{p_s}e^{i\theta_s}`$。标架等价为


```math
\theta_s\mapsto\theta_s+\gamma_0+\gamma_xx(s)+\gamma_yy(s)+\gamma_zz(s).
```


整体相位按射线识别；探针也随坐标标架运输。实际改变来源而固定探针不是纯标架更名。原语重相位在窗口代表上给 $`\gamma_y=\gamma_x+\gamma_z`$，是这里位置标架群的较窄子群。

**命题 C-13.2（整个相位环面的商）。** 四底角全非零时，唯一剩余圆周坐标为


<table><tbody><tr><td>

```math
\Phi=\theta_0+\theta_{13}-\theta_1-\theta_3\pmod{2\pi}.
```

</td></tr></tbody></table>


这是完整 $`(\mathbb{\text{ℝ}}/2\pi\mathbb{\text{ℤ}})`$ 商，沒有遗漏的有限规范类。零底角时按实际支持消去相位，回路不存在。

**证明。** 常数及 $`x,y,z`$ 的整数评价矩阵前四行（按 $`0,1,2,3`$）行列式 $`-1`$，整数核为原始向量 $`\mathbb{\text{ℤ}}d`$。更直接地，取 $`\gamma_0=-\theta_0,\gamma_x=\theta_0-\theta_1,\gamma_z=\theta_0-\theta_2,\gamma_y=\theta_0-\theta_3`$，四相位模 $`2\pi`$ 全部归零，余相位就是 $`\Phi`$。这给完整整数周期证明，超出仅 infinitesimal 核。若顶点缺失，忽略 $`\gamma_z`$ 仍只剩底面回路；缺任底角时相位评价行独立且相应整数树消元直接消去全部相位。$`\square`$

**命题 C-13.3（内部坐标与端点拓扑）。** 固定 $`0<Z<1,0<X,Y<r`$，在 $`\kappa_-<\kappa<\kappa_+`$ 定义


<table><tbody><tr><td>

```math
A=p_0p_{13},\quad B=p_1p_3,\quad
\chi=\frac{c_0c_{13}}{c_1c_3}=e^{u+i\Phi},\qquad
u=\frac12\log(A/B).
```

</td></tr></tbody></table>


有 $`du/d\kappa=\mathcal{\text{ℐ}}/2>0`$，$`u`$ 从 $`-\infty`$ 到 $`+\infty`$，故 $`\chi`$ 双射到 $`\mathbb{\text{ℂ}}^\times`$。闭纤维相位商由圆柱两端各压一点而拓扑同胚 $`S^2`$。

**证明。** 对数求导见 §4。下端点 $`A=0,B>0`$，上端点 $`B=0,A>0`$，所以极限成立。两端缺至少一个底角，§13.2 消去剩余相位；连续齐次坐标 $`[c_0c_{13}:c_1c_3]`$ 分别给 $`[0:1],[1:0]`$。区间乘圆的两端压缩就是圆周的悬挂，给球面拓扑。没有定义端点的 $`\arg0`$ 或零分母比。$`Z=0`$ 且 $`0<X,Y<1`$ 可删顶点重复此结论；$`r=0`$ 顶点、或 $`\omega=0`$ 侧面是单点商，可能 $`A=B=0`$，此时不使用 $`[0:0]`$。拓扑球面尚不保证光滑圆球度量，也不是物理位置空间。$`\square`$

## 14. 残差倒数成为相位水平线元

**定义 C-14.1（度量与水平最小化）。** 按 [C-L5] 射线几何背景，本卷自定无量纲 Fubini–Study 约定


<table><tbody><tr><td>

```math
ds_{\rm FS}^2=\langle d\psi,d\psi\rangle
-|\langle\psi,d\psi\rangle|^2
=\frac14\sum\frac{dp_s^2}{p_s}
+\sum p_s\,d\theta_s^2-(\sum p_s\,d\theta_s)^2.
```

</td></tr></tbody></table>


本式在正支撑内部使用。[C-L5] 的 $`2\hbar`$ 尺度不作本卷尺度。固定 $`X,Y,Z`$ 后，对声明标架等价取最短代表，得到关系线元。

**命题 C-14.2（同一回路的概率—相位几何）。** 内部关系线元为


<table><tbody><tr><td>

```math
ds_{\rm rel}^2=\frac{\mathcal{\text{ℐ}}}4d\kappa^2+
\frac1{\mathcal{\text{ℐ}}}d\Phi^2
=\frac1{\mathcal{\text{ℐ}}}(du^2+d\Phi^2).
```

</td></tr></tbody></table>


水平相位速度为 $`v_s=d_s\,d\Phi/(p_s\mathcal{\text{ℐ}})`$，与所有 $`1,x,y,z`$ 标架速度在 $`L^2(p)`$ 中正交。其行列式 $`1/4`$，面积元 $`\frac12d\kappa d\Phi`$，总面积


<table><tbody><tr><td>

```math
\mathcal{\text{𝒜}}_{\rm rel}=\pi\omega
=\pi\min\{X,Y,1-X-Z,1-Y-Z\}.
```

</td></tr></tbody></table>


**证明。** 把振幅微分代入定义，概率—相位交叉内积纯虚数，给分解。概率项 $`dp=d\,d\kappa`$ 立刻给 $`\mathcal{\text{ℐ}}/4`$。去整体相位令 $`\sum p_sv_s=0`$，固定 $`d\cdot v=d\Phi`$；Cauchy–Schwarz 给 $`(d\Phi)^2\le\mathcal{\text{ℐ}}\sum p_sv_s^2`$，所列速度达到等号。并且 $`\sum p_sv_sf_s=(d\Phi/\mathcal{\text{ℐ}})\sum d_sf_s=0`$ 对四标架函数都成立，确为完整水平最小化。相位系数正是 §4 的隐藏函数平方长度。$`du=\mathcal{\text{ℐ}} d\kappa/2`$ 给共形圆柱式，行列式与积分给面积。三角侧面宽度零使这条关系退化，未声明整个实际环境相位消失；$`1/4`$ 是约定归一化，不能解释为普朗克常数。$`\square`$

**命题 C-14.3（有限距离的锥形端点）。** 非退化纤维的每一端，用距离端点的参数 $`t>0`$，若有 $`m`$ 个底角概率在该端消失，则 $`m\in\{1,2\}`$，


```math
\mathcal{\text{ℐ}}=\frac mt+O(1),\quad
\rho=\int_0^t\frac{\sqrt{\mathcal{\text{ℐ}}(s)}}2ds
=\sqrt{mt}+O(t^{3/2}),\quad
\ell(t)=\frac{2\pi}{\sqrt{\mathcal{\text{ℐ}}(t)}}
=2\pi\sqrt{t/m}+O(t^{3/2}).
```


端点锥角 $`\lim\ell/\rho=2\pi/m`$。下端双零恰 $`X+Y=r`$，上端双零恰 $`X=Y`$；通常单零，双零给角 $`\pi`$。

**证明。** 逆式表明消失概率都等于 $`t`$，其余在非退化端有正极限，故信息主项 $`m/t`$。积分和倒平方根展开给式。相位圆周直径趋零，径向距离有限，所有该端 Cauchy 序列加入同一点；两端之间的正径向积分阻止合并，故内在度量完备化与两点拓扑紧化相符。近端相位系数为 $`\rho^2/m^2+O(\rho^4)`$，故可能是锥点而非平滑圆球。下端 $`p_0,p_{13}`$ 同零恰 $`X+Y=r`$，上端 $`p_1,p_3`$ 同零恰 $`X=Y`$。四种端点多重数组合均按此分类，不能把纯拓扑 $`S^2`$ 写成无条件光滑标准 Bloch 球。边界上的度量须在实际支撑重新定义，不把 $`\mathcal{\text{ℐ}}^{-1}`$ 当跨零概率的普通光滑坐标。$`\square`$

## 15. 不变两份比较、失败分支与真实记录

**假设 C-15.1（有限相干比较合同）。** 没有外加单位置相位参照；允许效果须对共同位置群不变。另供两份相同且相位相容的制备 $`|\psi\rangle\otimes|\psi\rangle`$，共同群作用 $`D\otimes D`$，以及指定联合投影和比较。这是两份制备资源，不是克隆未知态。准备耗尽后无自动重置、重抽或环境重入。

**命题 C-15.2（此实验类的最小份数及完整概率）。** 单份不变效果必对角，不能读 $`\Phi`$。两份的唯一非平凡无序总占位碰撞为 $`\{0,13\}`$ 与 $`\{1,3\}`$。固定有序分支


```math
|L\rangle=|0,13\rangle,\quad |R\rangle=|1,3\rangle,
\quad W=c_0c_{13}\overline{c_1c_3}=\sqrt{AB}e^{i\Phi}
```


后，所供比较态 $`|\pm_\theta\rangle=(e^{i\theta}|L\rangle\pm|R\rangle)/\sqrt2`$ 给无条件律


<table><tbody><tr><td>

```math
P_\pm(\theta)=\frac{A+B}2\pm\operatorname{Re}(e^{-i\theta}W),
\qquad P_{\rm fail}=1-A-B.
```

</td></tr></tbody></table>


$`\theta=0,\pi/2`$ 的概率差分别 $`2\operatorname{Re}W,2\operatorname{Im}W`$。

**证明。** 单份非对角元在共轭下乘 $`e^{i\gamma\cdot(v_s-v_t)}`$，不同顶点字符不同，故只能为零。两份无序对有十五个：含两顶点的总 $`z=2`$ 唯一；一顶点加底角的四个总 $`z=1`$ 互异；两个底角有十对，$`(x,y)`$ 和只在 $`(1,1)`$ 双重，正是两对角配对，故共有十四种总字符。有序交换的简并不是新的四角关系；所选 $`L,R`$ 不收另外两个交换分支，后二者归失败成本。相同总占位使此二维子空间不变，投影振幅 $`c_0c_{13},c_1c_3`$，Born 展开给完整式。均匀五态成功率 $`A+B=2/25`$，失败 $`23/25`$；该选定投影未声称最优不变成功率。$`AB=0`$ 时没有交叉读数；$`A+B=0`$ 时只有失败、不定义后选择态。两种设置提供总体概率的两正交分量，不意味着两个点击精确恢复未知参数。[C-L3] 的多份关系测量是背景，本四角概率由此直接证明。$`\square`$

**命题 C-15.3（条件关系球与非等距性）。** $`A+B>0`$ 的无记录成功态为


```math
\rho_{\rm pair}=\frac1{A+B}\begin{pmatrix}A&W\\\bar W&B\end{pmatrix}.
```


标准 Pauli 坐标是


<table><tbody><tr><td>

```math
\mathbf{\text{𝐛}}=(\operatorname{sech}u\cos\Phi,
-\operatorname{sech}u\sin\Phi,\tanh u),\quad\|\mathbf{\text{𝐛}}\|=1.
```

</td></tr></tbody></table>


其纯态 FS 拉回为 $`\frac14\operatorname{sech}^2u(du^2+d\Phi^2)`$，区别于 §14 的 $`\mathcal{\text{ℐ}}^{-1}(du^2+d\Phi^2)`$；单位 Bloch 球的圆度量还比此 FS 大四倍。最大熵补全对应整条赤道。

**证明。** 密度的右上元为 $`(b_x-ib_y)/2`$，故 $`b_y`$ 负号不可改；本比较约定的 $`\theta=\pi/2`$ 条件结果差对应 $`-\sigma_y`$，不是 $`\sigma_y`$。$`2\sqrt{AB}/(A+B)=\operatorname{sech}u,(A-B)/(A+B)=\tanh u`$，给单位长度。单位球微分直接为 $`\operatorname{sech}^2u(du^2+d\Phi^2)`$，二级纯态 FS 是其四分之一，亦可直接代入归一化两振幅。均匀五态在 $`u=0`$ 有 $`\mathcal{\text{ℐ}}^{-1}=1/20`$，条件 pair FS 系数 $`1/4`$，明确否定等距。$`A-B=\Delta`$，故最大熵 $`\Delta=0`$ 给 $`u=0`$、所有 $`\Phi`$，不是唯一相干态。pair 是成功条件接口，未把整个五维模式态认作一个量子位，也未删成功概率。$`\square`$

**假设 C-15.4（同一分支的真实记录）。** 另供成功分支同一制备中的单位记录 $`e_L,e_R`$，$`\eta_{\rm rec}=\langle e_R,e_L\rangle`$。具体的记录取得合同供应如下等距映射：对所选分支的正交补取正交基 $`|F_k\rangle`$，取单位失败记录 $`f_k`$ 与正交结果旗标，规定


```math
V_{\rm rec}|L\rangle=|{\rm ok}\rangle|L\rangle e_L,\qquad
V_{\rm rec}|R\rangle=|{\rm ok}\rangle|R\rangle e_R,\qquad
V_{\rm rec}|F_k\rangle=|{\rm fail}\rangle|F_k\rangle f_k.
```


各像的正交性由分支及旗标保证，即使记录不正交也有 $`V_{\rm rec}^\dagger V_{\rm rec}=I`$。读取旗标得到成功或失败；忽略成功记录后非对角条目为 $`\eta_{\rm rec}W`$。记录相位约定随实际分支共同运输。此映射属于明确供应的实验资源，数学存在不等于已经取得。

**命题 C-15.5（可见度与记录操作边界；[C-R4] §108）。** $`|\eta_{\rm rec}|\le1`$，pair 状态为


```math
\rho_{{\rm pair},\eta}=\frac1{A+B}
\begin{pmatrix}A&\eta_{\rm rec}W\\\bar\eta_{\rm rec}\bar W&B\end{pmatrix}.
```


若 $`\mathcal{\text{𝒫}}=|A-B|/(A+B),\mathcal{\text{𝒱}}=2|\eta_{\rm rec}|\sqrt{AB}/(A+B)`$，则


<table><tbody><tr><td>

```math
\mathcal{\text{𝒫}}^2+\mathcal{\text{𝒱}}^2=
1-\frac{4AB}{(A+B)^2}(1-|\eta_{\rm rec}|^2).
```

</td></tr></tbody></table>


$`AB>0`$ 时纯态恰 $`|\eta_{\rm rec}|=1`$，严格小于一时混态；$`AB=0`$ 时是纯极点且可见度零。实际读出的是 $`\eta_{\rm rec}W`$，只有已知非零记录重叠及 $`AB>0`$ 才能恢复原 $`\Phi`$。

**证明。** 同一联合分支密度取记录迹得矩阵，Cauchy–Schwarz 给模长界。行列式 $`AB(1-|\eta_{\rm rec}|^2)/(A+B)^2`$ 给纯混条件；$`(A-B)^2+4AB=(A+B)^2`$ 给可见度式。记录相位把有效相位改为 $`\Phi+\arg\eta_{\rm rec}`$，不改对角概率。对任意仅记录上的迹保持映射 $`\Lambda`$，


```math
\operatorname{Tr}_{E'}[(\operatorname{id}\otimes\Lambda)\Omega]
=\operatorname{Tr}_E\Omega,
```


因为对系统观测 $`A_0`$ 的配对中 $`\Lambda^\dagger(I)=I`$。所以无条件删除、改写记录不能恢复局部相干；条件测量反馈或联合逆操作须另供。$`\square`$

**命题 C-15.6（有限菜单中的充分边界）。** 此合同的公开边界含来源标识、标架、准备份数、阶段、费用、实际 success/failure 档案和可请求设置。初始联合投影成功质量 $`s=A+B`$，失败质量 $`1-s`$；失败终止。正质量成功后保留 $`\rho_{{\rm pair},\eta}`$，可选一次比较设置，结果 $`\pm`$ 后终止。$`(p,W,\eta_{\rm rec})`$ 连同公开边界决定全部有限分支律及后继；仅 $`p`$ 一般不足。

**证明。** 成功支按 $`s>0`$ 归一化；比较的条件概率是命题 C-15.2 交叉项改为 $`\eta_{\rm rec}W`$ 后除 $`s`$，正性由该二级密度保证。零质量支不设置后验，资源在投影和比较时各依合同消耗，没有新增重试权限。相同边界给相同菜单、概率及终止标签，逐阶段归纳证明全部允许有限历史。均匀概率 $`\Phi=0,\pi`$ 在 $`\theta=0`$ 的成功结果完全相反；同 $`\chi`$ 而 $`\eta_{\rm rec}=1,0`$ 则干涉与无干涉不同，证明遗漏项可被菜单读取。若明确允许有限独立批次重复和未知源先验，正证据质量时用整参数后验 $`\pi(d\lambda\mid h)\propto P(h\mid\lambda)\pi(d\lambda)`$ 更新；仅后验均值不一般充分。基本合同终止后没有该附加资源。$`\square`$

## 16. 双窗接缝：边缘可拼接的三角条件

**定义 C-16.1（同一高到低双窗域）。** 第一个实际窗口 $`i`$、第二个 $`j`$ 的守卫为 $`x(i)y(j)=0`$。令


```math
R_1=\{1,13\},\quad C_1=\{3,13\},\quad
R_0=\Sigma\setminus R_1,\quad C_0=\Sigma\setminus C_1,
\quad E=(\Sigma\times\Sigma)\setminus(R_1\times C_1).
```


$`E`$ 有二十一个合法格。联合律 $`p_{ij}\ge0`$ 归一化，其完整边缘 $`\mu_i,\nu_j`$ 各归一化，置 $`a=\sum_{R_1}\mu_i,b=\sum_{C_1}\nu_j,c=1-a-b`$。本章 $`a,b,c`$ 是接缝质量，区别于 §9 的复重叠。

**命题 C-16.2（可行性及显式共同补全）。** 边缘可由此同一合法域实现，当且仅当 $`a+b\le1`$。若 $`a,b<1`$，一份补全为


<table><tbody><tr><td>

```math
p^*_{ij}=\begin{cases}
0,&R_1\times C_1,\\
\mu_i\nu_j/(1-b),&R_1\times C_0,\\
\mu_i\nu_j/(1-a),&R_0\times C_1,\\
c\mu_i\nu_j/[(1-a)(1-b)],&R_0\times C_0.
\end{cases}
```

</td></tr></tbody></table>


$`a=1`$ 强制 $`b=0`$，此时仅在 $`R_1\times C_0`$ 取 $`\mu_i\nu_j`$；$`b=1`$ 对称处理。

**证明。** 第一窗低位占用、第二窗高位占用是互斥事件，给必要性。对 $`i\in R_1`$，求行和为 $`\mu_i`$；$`i\in R_0`$ 时两块行和为 $`\mu_i[b/(1-a)+c/(1-a)]=\mu_i`$。列和对称给 $`\nu_j`$，全部非负且归一化，证明充分性。$`a=0,b=0`$ 时对应组所有非负边缘为零，删除这些零行列，公式无 $`0/0`$；$`c=0`$ 时第三块零；$`a=1`$ 或 $`b=1`$ 用专门分支。三角形 $`(a,b)\ge0,a+b\le1`$ 只分类接缝两占位的共同律，未确定二十一个模式配对质量、原始联合树或未知真实来源。$`\square`$

## 17. 可用支撑、十二个回路与目标恢复

**定义 C-17.1（边缘核与整个纤维支撑）。** 对格数组边缘映射 $`\mathcal{\text{𝒜}} p=(\sum_jp_{ij},\sum_ip_{ij})`$。$`\mathcal{\text{ℱ}}(\mu,\nu)`$ 是全部合法非负相容律。定义


```math
E_{\rm adm}=\{e:\text{存在 }p\in\mathcal{\text{ℱ}}(\mu,\nu)\text{ 使 }p_e>0\}.
```


它区别于单一 $`p`$ 的 $`E(p)=\operatorname{supp}p`$；前者决定整个纤维仿射维数，后者决定该点固定支撑面和相位商。

**命题 C-17.2（原生全合法域的精确循环接口）。** 在全 $`E`$ 实格空间上 $`\operatorname{rank}\mathcal{\text{𝒜}}=9`$，归一化联合维数二十、完整边缘维数八、核维数十二。对合法 $`i,j\ne0`$ 定义


```math
D^{ij}=E_{ij}+E_{00}-E_{i0}-E_{0j}.
```


十二个 $`D^{ij}`$ 是核的基，同边缘数组恰满足


<table><tbody><tr><td>

```math
p'-p=\sum_{i,j\ne0,(i,j)\in E}(p'_{ij}-p_{ij})D^{ij}.
```

</td></tr></tbody></table>


边缘全正且 $`a+b<1`$ 时，$`p^*`$ 全合法格正，纤维确为十二维；$`p=p^*+Dt`$ 必须同时满足二十一项非负。

**证明。** 空行空列与所有模式合法，每个四角确在 $`E`$；各行列和零。对核数组，内部格固定后，零列为负行和、零行为负列和、$`00`$ 为内部总和，证明唯一展开；各内部格是独有单位坐标，证明独立。内部格数 $`4\cdot4-2\cdot2=12`$，故秩 $`21-12=9`$。两个归一化边缘各四参数，共八；一个联合归一化条件使二十一减一。二部图有十个顶点、二十一条边且连通；将列端行符号反转后边缘矩阵是有向关联矩阵，秩十减一，循环数 $`21-10+1=12`$。锚行列九边构成生成树，所列是基本循环。整数核同样由其唯一整数内部格系数生成，但整数格点和可行实切线不是同一个参数域。正 $`p^*`$ 允许各方向正负小扰动，证明维数；概率不等式耦合这些方向，不授予十二个独立操作旋钮。[C-L6] 是运输多面体背景，禁止格的此具体计算由本证明承担。$`\square`$

**命题 C-17.3（饱和及所有零边缘的维数）。** 正边缘且 $`a+b=1`$ 时，$`R_0\times C_0`$ 全被强制零，可用图 $`K_{2,3}\sqcup K_{3,2}`$，纤维维数四。一般非空纤维的维数为


<table><tbody><tr><td>

```math
|E_{\rm adm}|-|V_{\rm adm}|+k_{\rm adm},
```

</td></tr></tbody></table>


其中 $`V_{\rm adm}`$ 是实际非孤立顶点，$`k_{\rm adm}`$ 是其连通分量数。

**证明。** 合法三块质量必须分别为 $`a,b,c`$，所以 $`c=0`$ 强制整个余块零。两个正边缘矩形各维 $`(2-1)(3-1)=2`$，共四；图也给 $`12-10+2=4`$。一般情形，对每个可用边选一份使其正的相容律，再有限平均，得到在整个 $`E_{\rm adm}`$ 全正的相对内部点。该点允许全部边缘核的小正负方向，故仿射维数等于限制边缘矩阵核维数。关联矩阵每连通分量的左核只含常数，秩 $`|V|-k`$，即得公式。单个稀疏顶点的支持可能只是树，固定支撑面维零，整个纤维却仍十二维；不得用该单点支持取代 $`E_{\rm adm}`$。零 $`00`$ 时锚四角比失去定义，改用实际图的生成森林循环，亦不能把一侧可进入新边的切锥误作固定支撑双侧线性核。$`\square`$

**命题 C-17.4（哪些任务只消费边缘）。** 全合法支撑严格正的固定纤维上，实目标 $`f`$ 的期望由边缘识别，当且仅当所有十二个


```math
J_{ij}(f)=f_{ij}+f_{00}-f_{i0}-f_{0j}
```


为零，当且仅当合法格上 $`f_{ij}=A_i+B_j`$。一般退化纤维应改用实际 $`E_{\rm adm}`$ 的边缘核正交条件。

**证明。** 命题 C-17.2 的唯一展开给 $`\mathbb{\text{𝔼}}_{p'}f-\mathbb{\text{𝔼}}_pf=\sum(p'_{ij}-p_{ij})J_{ij}(f)`$。全正点允许每方向双侧小扰动，给必要性，反向直接相消。$`A_i=f_{i0},B_j=f_{0j}-f_{00}`$ 给势分解。一般图中相同证明对循环核使用，等价于目标在可用图上为行列势；各连通分量独立处理。不可对退化纤维强求所有全图 $`J`$ 零。$`\square`$

**命题 C-17.5（同原生历史的二阶消费者；[C-R2] 命题 8.7–8.8）。** 后文二值 $`A,B\in\{0,1\}`$ 的一表示中间模式 $`2`$，不表示全局模式 $`1`$。两窗只输入空／中间，真实共享接缝恒零，原生终值


```math
Q=13A+3B.
```


$`P_+=\frac12\delta_{00}+\frac12\delta_{11}`$、$`P_-=\frac12\delta_{01}+\frac12\delta_{10}`$ 有相同完整局部边缘，均值八，但平方矩 $`128,89`$，$`J(Q^2)=78`$。

**证明。** $`\beta=(0,1)^{\mathsf{\text{𝖳}}}`$，同态第二窗组成 $`AS\beta+B\beta`$，施 $`q`$ 给式。前一律 $`Q=0,16`$，后一律 $`3,13`$，直接平方取半得 $`128,89`$；$`16^2-3^2-13^2=78`$。数量可加目标 $`J(Q)=0`$，平方首次读到共同出现。若从同一执行追加空窗，$`Q'=55A+13B`$，仍是原生推进而非复位。首窗实际回复零时，两律的第二回复分别确定零、三，故不仅是无条件目标比较。面积／体积型交叉项是混合响应类型，不新增物理维数。$`\square`$

**命题 C-17.6（服从接缝的最大熵补全）。** 命题 C-16.2 的 $`p^*`$ 唯一最大化固定完整边缘的熵；在 $`E_{\rm adm}`$ 上


<table><tbody><tr><td>

```math
H(p^*)-H(p)=\operatorname{KL}(p\Vert p^*)\ge0.
```

</td></tr></tbody></table>


严格内部每合法锚四角有 $`p^*_{ij}p^*_{00}=p^*_{i0}p^*_{0j}`$，但一般 $`p^*\ne\mu\nu`$。

**证明。** 内部的三块系数分别 $`1/(1-b),1/(1-a),c/[(1-a)(1-b)]`$，其对数可写行势加列势：例如在 $`R_0,C_0`$ 加公共常数 $`\log[c/((1-a)(1-b))]`$，$`R_1`$ 再加 $`\log[(1-a)/c]`$，$`C_1`$ 再加 $`\log[(1-b)/c]`$。非法块不使用该表达。故 $`\log p^*`$ 加上 $`\log\mu_i+\log\nu_j`$ 后仍为行列势，相同边缘消去交叉熵差；KL 非负与唯一等号见 §3。零边缘删行列；$`c=0`$ 时各实际矩形分量的系数仍行列可分，$`a=1,b=1`$ 专门支持亦为乘积，同证明成立。强制零边共同删除，$`0\log0=0`$，不对零项取对数或比值。均匀边缘 $`a=b=2/5,c=1/5`$，两占用块每格 $`1/15`$，余块 $`1/45`$；独立乘积 $`1/25`$ 给非法格正质量，合法格均匀 $`1/21`$ 的行列质量分别 $`3/21`$ 或 $`5/21`$，亦非所给均匀边缘。约束强制依赖与额外循环偏好分开；最大熵不代表实际未知联合源已取得。$`\square`$

## 18. 接缝循环的相干商、耦合几何与支撑纠缠

**假设 C-18.1（合法二部纯态）。** 另供 $`\mathbb{\text{ℂ}}^5\otimes\mathbb{\text{ℂ}}^5`$ 中 $`|\Psi\rangle=\sum_{(i,j)\in E}c_{ij}|i,j\rangle`$，$`|c_{ij}|^2=p_{ij}`$。全合法振幅先取非零，局部模式标架 $`c_{ij}\mapsto e^{i\alpha_i+i\beta_j}c_{ij}`$。源和探针共同运输；此群不同于单窗的位置群。

**命题 C-18.2（十二个完整环面坐标）。**


<table><tbody><tr><td>

```math
\chi_{ij}=\frac{c_{ij}c_{00}}{c_{i0}c_{0j}},\quad
|\chi_{ij}|^2=\frac{p_{ij}p_{00}}{p_{i0}p_{0j}},\quad
\Phi_{ij}=\arg\chi_{ij}.
```

</td></tr></tbody></table>


固定全概率后相位商为 $`(\mathbb{\text{ℝ}}/2\pi\mathbb{\text{ℤ}})^{12}`$，上述坐标完整，沒有隐含有限类。实际零支撑图则改用其独立循环数。

**证明。** 四相位逐项抵消。取 $`\alpha_0=-\theta_{00},\beta_0=0,\alpha_i=-\theta_{i0},\beta_j=\theta_{00}-\theta_{0j}`$，将零行零列九个锚相位归零，内部余相位恰为 $`\Phi_{ij}`$。十个局部相位参数有整体一项冗余，作用秩九；九边生成树的单位系数消元在整数环面上成立，给精确 $`2\pi`$ 周期和十二商圆。零振幅改用实际图生成森林，每分量一个相位冗余，商循环数 $`|E(p)|-|V(p)|+k(p)`$；不定义 $`\arg0`$ 或零锚分母。$`\square`$

**命题 C-18.3（两份平衡循环比较的完整合同）。** 另供两份相同、相位相容的 $`|\Psi\rangle`$ 产品制备及共同局部模式参照，选择有序


```math
|L_{ij}\rangle=|(i,j),(0,0)\rangle,\qquad
|R_{ij}\rangle=|(i,0),(0,j)\rangle.
```


两分支具有相同每侧模式多重集。采用与 §15 一致的比较相位约定，


```math
s_{ij}=p_{ij}p_{00}+p_{i0}p_{0j},\qquad
W_{ij}=c_{ij}c_{00}\overline{c_{i0}c_{0j}},
```


<table><tbody><tr><td>

```math
P_\pm(\theta)=s_{ij}/2\pm\operatorname{Re}(e^{-i\theta}W_{ij}),
\quad P_{\rm fail}=1-s_{ij}.
```

</td></tr></tbody></table>


**证明。** 局部标相因相同多重集给共同因子，故所供联合投影不变。两个投影振幅直接 Born 展开得到式；$`|W_{ij}|^2=p_{ij}p_{00}p_{i0}p_{0j}`$ 保证非负，$`s_{ij}\le1`$ 是两个正交分支的总质量。零成功支不条件化；缺任角时交叉项零。$`\theta=\pi/2`$ 取正虚部的差，此符号固定。记录若另供，必须来自本同一制备：$`\Gamma=\langle e_{i0}\otimes e_{0j},e_{ij}\otimes e_{00}\rangle`$ 将交叉项乘 $`\Gamma`$；不得拼来自独立不相容源的记录。准备、联合投影、失败和各批消耗同 §15 的阶段合同，未知参数不由一次点击取得。$`\square`$

**命题 C-18.4（共享锚使 Fisher 与相位几何耦合）。** 全正合法 $`p=p^*+Dt`$，完整配对结果实验的信息矩阵


```math
\mathscr{\text{ℐ}}=D^{\mathsf{\text{𝖳}}}\operatorname{diag}(1/p)D>0,
```


<table><tbody><tr><td>

```math
\mathscr{\text{ℐ}}_{(ij),(kl)}=\frac1{p_{00}}
+\frac{\mathbf{\text{𝟏}}_{i=k}}{p_{i0}}
+\frac{\mathbf{\text{𝟏}}_{j=l}}{p_{0j}}
+\frac{\mathbf{\text{𝟏}}_{i=k,j=l}}{p_{ij}}.
```

</td></tr></tbody></table>


按本卷 FS 约定，对局部模式标架水平最小化得


<table><tbody><tr><td>

```math
ds^2=\tfrac14dt^{\mathsf{\text{𝖳}}}\mathscr{\text{ℐ}}\,dt+
 d\Phi^{\mathsf{\text{𝖳}}}\mathscr{\text{ℐ}}^{-1}d\Phi.
```

</td></tr></tbody></table>


**证明。** 得分列为 $`D_e/p_e`$，平方期望给信息式；$`D`$ 列独立且所有 $`p_e>0`$ 给正定。两循环的共享 $`00,i0,0j`$ 内积给四项条目。概率 FS 为四分之一 $`\sum dp_e^2/p_e`$。相位速度满足 $`D^{\mathsf{\text{𝖳}}}v=d\Phi`$，加权最小范数解


```math
v=\operatorname{diag}(1/p)D\mathscr{\text{ℐ}}^{-1}d\Phi.
```


因为 $`\mathcal{\text{𝒜}} D=0`$，对每个行列局部势 $`g=\mathcal{\text{𝒜}}^{\mathsf{\text{𝖳}}}\gamma`$，$`g^{\mathsf{\text{𝖳}}}\operatorname{diag}(p)v=\gamma^{\mathsf{\text{𝖳}}}\mathcal{\text{𝒜}} D\mathscr{\text{ℐ}}^{-1}d\Phi=0`$，包括常量平均相位零。任一其他解与此正交相差局部势，勾股给最小值 $`d\Phi^{\mathsf{\text{𝖳}}}\mathscr{\text{ℐ}}^{-1}d\Phi`$。边界须在实际正支撑的独立循环上重算，不能延伸十二维逆矩阵；此度量不使循环成为独立物理旋钮或空间轴。$`\square`$

**命题 C-18.5（全部合法四角比一仍有支撑纠缠）。** 真实另供正平方根纯态 $`|\Psi_*\rangle=\sum\sqrt{p^*_{ij}}|i,j\rangle`$。对正质量组，取


```math
|R_k\rangle=\sum_{i\in R_k}\sqrt{\mu_i/\mu(R_k)}|i\rangle,
\quad |C_k\rangle=\sum_{j\in C_k}\sqrt{\nu_j/\nu(C_k)}|j\rangle.
```


删除零组后有


```math
|\Psi_*\rangle=\sqrt c|R_0C_0\rangle+\sqrt b|R_0C_1\rangle+
\sqrt a|R_1C_0\rangle,
\quad A_* =\begin{pmatrix}\sqrt c&\sqrt b\\\sqrt a&0\end{pmatrix},
```


其 Schmidt 概率（零项删除）为


<table><tbody><tr><td>

```math
\lambda_\pm=(1\pm\sqrt{1-4ab})/2.
```

</td></tr></tbody></table>


秩二恰 $`ab>0`$；完整边缘全正且 $`a+b<1`$ 时，所有合法 $`\chi_{ij}=1`$。均匀边缘谱 $`4/5,1/5`$。

**证明。** 各组正交，三合法块内平方根振幅分别因子化，逐格对回 §16 的 $`p^*`$，质量 $`c,b,a`$。$`\operatorname{tr}A_*A_*^\dagger=1`$，$`\det A_*A_*^\dagger=ab`$，解特征方程给式；$`ab\le1/4`$ 由 $`a+b\le1`$。$`a=0`$ 或 $`b=0`$ 删除零组后秩一；$`a=1,b=0`$ 和对称端点也是秩一。饱和 $`c=0,a,b>0`$ 仍秩二，但 $`00`$ 锚为零，不能继续声称十二个 $`\chi`$ 都定义。内部概率四角比一、振幅全正给 $`\chi=1`$，禁止块本身阻止乘積；四角只描述合法支撑内额外偏好。经典对角混合 $`\sum p^*_{ij}|i\rangle\langle i|\otimes|j\rangle\langle j|`$ 显然可分。纯态需要真实联合相干制备，不从原生禁止格自动获得物理纠缠。$`\square`$

## 19. 共同中心的高阶消元与低秩表示

一般双窗纤维中的十二方向不能由合法性独自选定。另一种明确的星形生成合同说明：多个高阶系数也可以全部由同一个隐藏中心决定；重新保留该中心会恢复特殊低秩因子结构。

### 19.1 一个隐藏中心生成受约束的高阶项

**定义 C-19.1（另行声明的星形来源）。** 对整数 $`d\ge1`$，取
$`z,x_1,\ldots,x_d\in\{0,1\}`$，约束 $`zx_i=0`$，外围之间无排斥。令外围活动 $`a_i>0`$、中心活动 $`b>0`$，完整源权为
$`b^z\prod_i a_i^{x_i}`$。$`z=0`$ 时允许全部 $`2^d`$ 外围配置，$`z=1`$ 时只允许全零，故


<table><tbody><tr><td>

```math
\text{支撑配置数}=2^d+1,\qquad
\mathcal{\text{𝒵}}_\star=\prod_{i=1}^d(1+a_i)+b.
```

</td></tr></tbody></table>


配置数与配分总权不同。这是受控 $`d`$ 叶扩展协议，不是原生路径自动增加的动作菜单。

**占位凸几何。** 在明确坐标 $`(X_1,\ldots,X_d,Z)`$ 中，


<table><tbody><tr><td>

```math
\begin{aligned}
\mathcal{\text{𝒫}}_\star
&=\operatorname{conv}\bigl(([0,1]^d\times\{0\})
\cup\{(0,\ldots,0,1)\}\bigr)\\
&=\{Z\ge0,\ X_i\ge0,\ X_i+Z\le1\ (1\le i\le d)\}.
\end{aligned}
```

</td></tr></tbody></table>


**证明。** 每个合法顶点满足不等式。反向它们先给 $`0\le Z\le1`$；若 $`Z<1`$，点
$`(X_1/(1-Z),\ldots,X_d/(1-Z))`$ 在单位立方体，按各坐标二分乘积权写成其顶点的凸组合，再以权 $`1-Z`$ 与中心顶点权 $`Z`$ 混合。若 $`Z=1`$，所有 $`X_i=0`$，只剩中心。$`0,e_1,\ldots,e_d,e_z`$ 仿射独立，故维数为 $`d+1`$。固定高度截面为 $`[0,1-Z]^d`$。$`\square`$

| 外围数 $`d`$ | 合法配置数 | 占位凸几何 | 仿射维数 |
| ---: | ---: | --- | ---: |
| $`1`$ | $`3`$ | 三角形 | $`2`$ |
| $`2`$ | $`5`$ | 正方形底金字塔 | $`3`$ |
| $`3`$ | $`9`$ | 立方体底四维锥体 | $`4`$ |

维数属于占位坐标模型。

**定理 C-19.2（中心消元与唯一多线性系数）。** 对同一个中心求和后，


<table><tbody><tr><td>

```math
W_\star(x)=\left(\prod_i a_i^{x_i}\right)\Psi_b(x),
\qquad \Psi_b(x)=1+b\prod_{i=1}^d(1-x_i).
```

</td></tr></tbody></table>


令 $`L_b=\log(1+b)>0`$，在外围 Boolean 立方体上，


<table><tbody><tr><td>

```math
\log\Psi_b(x)=L_b\prod_i(1-x_i)
=L_b\sum_{S\subseteq[d]}(-1)^{|S|}
\prod_{i\in S}x_i.
```

</td></tr></tbody></table>


**证明。** 外围全零时中心两值权和为 $`1+b`$，否则中心只可为零，权一。Boolean 乘积 $`\prod_i(1-x_i)`$ 仅取零、一，所以取对数给第一式；展开乘积给第二式。

为证明多线性表示唯一，令 $`f(x)=\sum_Sc_S\prod_{i\in S}x_i`$，在集合 $`T`$ 的指示点 $`1_T`$ 上，
$`f(1_T)=\sum_{S\subseteq T}c_S`$。从空集起按集合大小归纳，先前系数已知后唯一确定 $`c_T`$；等价地
$`c_S=\sum_{T\subseteq S}(-1)^{|S|-|T|}f(1_T)`$。故显示的系数全部唯一，最高项为 $`(-1)^dL_b\ne0`$，无法用更低次数项替换。$`\square`$

特别 $`d=3`$ 的全部项为


<table><tbody><tr><td>

```math
\log\Psi_b=L_b\bigl(
1-x_1-x_2-x_3+x_1x_2+x_1x_3+x_2x_3-x_1x_2x_3
\bigr).
```

</td></tr></tbody></table>


单外围只有单点修正，双外围第一次有 $`xy`$ 联合项，三外围有无法用单点和两两项替代的对数三元项。但所有非恒定系数都由同一个 $`b`$ 决定；它们不是可独立调节的 $`2^d-1`$ 个参数。外围单点活动只添加 $`\sum_i x_i\log a_i`$。

五模式的最小性只属于此协议：一个隐藏二值中心、两个可共同选择的自由外围，第一次能产生二元四角项，支撑为五种。$`d=1`$ 尚无两个外围方向，$`d=2`$ 才有正方形回路。它不指定普遍理论的基础数，也不把另供星形等同于原生长路径。这里有限消元的邻域因子由§7.4的成熟步骤生成，Boolean 系数唯一性承担这份特殊因子的完整表示。[^CE-VE]

### 19.2 保留一个共同中心与跨侧秩二

把同一中心作为潜在指标重新保留，恒等式是


<table><tbody><tr><td>

```math
\Psi_b(x)=\sum_{z=0}^1b^z
\prod_{i=1}^d\mathbf{\text{𝟏}}_{\{zx_i=0\}}.
```

</td></tr></tbody></table>


这是原来的共同 $`z`$，活动 $`b`$ 只计一次。把中心分别复制成左右独立变量会改变来源。

**定理 C-19.3（所有非空分割的精确秩）。** 对 $`A\sqcup B=[d]`$、$`A,B`$ 都非空，令 $`e_A,e_B`$ 分别为两侧全零配置的指示列向量，$`\mathbf{\text{𝟏}}_A,\mathbf{\text{𝟏}}_B`$ 为全一列向量。把 $`\Psi_b`$ 按两侧全部配置展成矩阵，则


<table><tbody><tr><td>

```math
\Psi_b=\mathbf{\text{𝟏}}_A\mathbf{\text{𝟏}}_B^{\mathsf{\text{𝖳}}}
+b\,e_Ae_B^{\mathsf{\text{𝖳}}},\qquad
\operatorname{rank}\Psi_b=2.
```

</td></tr></tbody></table>


**证明。** 两个外积给秩至多二。每侧选全零及一个非零配置，得到子矩阵


```math
\begin{pmatrix}1+b&1\\1&1\end{pmatrix}
```


的行列式 $`b>0`$，故秩至少二。外围正活动因子在展平矩阵上形成可逆正对角行、列缩放，所以完整 $`W_\star`$ 也保秩二。$`\square`$

$`b=0`$ 时秩一；空侧时矩阵只有一行或一列，秩一；$`d=1`$ 没有两侧都非空的分割。若要求精确跨侧乘积项表示，一项只能给秩一，故两项是该表示任务中的最少项数。

这把高阶来源与低秩边界的关系说清：消去共同变量产生高阶对数项，重新保留共同变量则恢复局部因子拼接。§7.4的消元次序背景在此被实际消费；把中心先消掉的稠密表有 $`2^d`$ 个外围格，但此特殊来源仍有已证明的两项结构。一般稠密表的复杂度背景不能用来否定该结构，也不能从该结构推断任意高阶律都秩二。[^CE-VE][^CE-G]

$`d=2`$、$`(a_1,a_2)=(a,c)`$ 时 $`W_\star`$ 正好是§7.2的 $`W`$，其秩二来源直接进入命题 C-7.6 的 $`00`$ 后验下一回复任务。共同二态指标、一个中心参数、全部外围活动、响应矩阵的线性秩、数值精度、完整历史档案及设备成本是不同资源；重新引入潜变量不等于取得该次隐藏结果，秩二也不说明总体只需一比特存储。

同源接缝的其他模型还必须保留自己的支撑和联合条件。例如双窗禁止块是第一窗 $`x=1`$ 与第二窗 $`y=1`$ 的四个模式对，剩余二十一格；该支撑上的任意联合律仍有边缘未决定的循环参数。这里星形的两个外积和下一节正平方根路径的两个切口向量只刻画指定因子化子族，不删除二十一格来源或有限奇偶来源的额外关系。[^CE-C][^CE-S]

## 20. 因子化相干链的真实切口与共同记录

§8 的经典端点近独立没有决定内部相干切口。这里另供相位一致的正平方根制备，证明每个真实切口的精确秩；其因子化假设与§18的一般合法支撑相干商分别保留。

### 20.1 额外相干制备、真实切口与关系综合

**定义 C-20.1（另供的正平方根纯态）。** 在固定正交张量基
$`\mathcal{\text{ℋ}}_N=(\mathbb{\text{ℂ}}^2)^{\otimes N}`$ 中，另外供应共同相位和实际相干制备


<table><tbody><tr><td>

```math
|\Psi_N\rangle=
\frac1{\sqrt{\mathcal{\text{𝒵}}_N}}
\sum_{\text{合法 }b}
\sqrt{\prod_iw_i^{b_i}}\,
|b_1\cdots b_N\rangle.
```

</td></tr></tbody></table>


范数平方为 $`\sum_b\omega(b)/\mathcal{\text{𝒵}}_N=1`$。经典权重只定义对角概率，不自动授予这个纯态、相位参照、联合控制或测量。单窗振幅记为 $`c_\sigma=\sqrt{p_\sigma}`$，其底面满足
$`c_0c_{13}=c_1c_3`$，所以全正支撑的平方回路比 $`\chi=c_0c_{13}/(c_1c_3)=1`$。这是指定正相位及 $`p_0p_{13}=p_1p_3`$ 的结果。等五质量时，只把 $`c_{13}`$ 改为负的另供制备具有相同 $`P`$，却给 $`\chi=-1`$；端点逆式恢复概率而不恢复这种相位关系。是否能比较两制备仍取决于所供相干操作和共同记录。

**定理 C-20.2（正因子化制备的精确切口秩）。** 对 $`N\ge2`$、真正切口 $`1\le k<N`$，定义


```math
\begin{aligned}
|L_s\rangle&=
\sum_{\substack{b_1,\ldots,b_k\text{ 合法}\\b_k=s}}
\sqrt{\prod_{i=1}^kw_i^{b_i}}\,
|b_1\cdots b_k\rangle,\\
|R_t\rangle&=
\sum_{\substack{b_{k+1},\ldots,b_N\text{ 合法}\\b_{k+1}=t}}
\sqrt{\prod_{i=k+1}^Nw_i^{b_i}}\,
|b_{k+1}\cdots b_N\rangle .
\end{aligned}
```


则


<table><tbody><tr><td>

```math
|\Psi_N\rangle=
\frac{|L_0\rangle\otimes(|R_0\rangle+|R_1\rangle)
+|L_1\rangle\otimes|R_0\rangle}{\sqrt{\mathcal{\text{𝒵}}_N}},
```

</td></tr></tbody></table>


且此切口 Schmidt 秩恰为二，纠缠熵以比特计满足 $`0<S_{\mathrm{cut}}\le1`$。

**证明。** 左右内部合法性已各自计入；跨切口只禁止 $`11`$，另外三种配对全部允许，因子化平方根权遂给显示的三项。两侧零、一组各有不交的正交基支撑，因此同侧向量正交。每侧非空，全部零位串和只把触边位设一的位串分别属于两组；正活动使四向量均非零。

令 $`\ell_s=\|L_s\|^2>0,\ r_t=\|R_t\|^2>0`$。归一化四组向量后，在两侧正交单位基中的系数矩阵为


```math
C_{\mathrm{cut}}=
\frac1{\sqrt{\mathcal{\text{𝒵}}_N}}
\begin{pmatrix}
\sqrt{\ell_0r_0}&\sqrt{\ell_0r_1}\\
\sqrt{\ell_1r_0}&0
\end{pmatrix},
\qquad
\det C_{\mathrm{cut}}
=-\frac{\sqrt{\ell_0\ell_1r_0r_1}}{\mathcal{\text{𝒵}}_N}\ne0.
```


二侧纯态的 Schmidt 系数是系数矩阵的奇异值，故秩恰为二。这是既有 Schmidt/SVD 工具和等振幅合法链秩至多二证明的正权精确秩应用。[^CE-S] 两个约化谱概率为 $`\lambda,1-\lambda`$，$`0<\lambda<1`$。其熵
$`h_2(\lambda)=-\lambda\log_2\lambda-(1-\lambda)\log_2(1-\lambda)`$ 严格正；导数为
$`\log_2((1-\lambda)/\lambda)`$，二阶导数
$`-1/((\ln2)\lambda(1-\lambda))<0`$，唯一最大点 $`1/2`$ 给一比特。$`\square`$

例如 $`N=2,\ w=(4,9)`$，


```math
|\Psi_2\rangle=\frac{|00\rangle+3|01\rangle+2|10\rangle}{\sqrt{14}},
\quad C_{\mathrm{cut}}=\frac1{\sqrt{14}}
\begin{pmatrix}1&3\\2&0\end{pmatrix},
\quad\det C_{\mathrm{cut}}=-\frac37.
```


$`N=1`$ 没有真实两侧切口；人为给空侧时只有秩一、熵零。零活动导致某些组消失，须按实际支撑另算，不能延用严格非零下界。任意相干振幅即使同样支撑于合法位串，也不必因子化；固定零接缝可制备
$`F_{m+1}^{-1/2}\sum_{u\in\mathcal{\text{𝒲}}_{m-1}}|u0\rangle\otimes|0u\rangle`$，
$`\mathcal{\text{𝒲}}_{m-1}`$ 为合法长 $`m-1`$ 词，其正交 Schmidt 秩为 $`F_{m+1}`$。这是既有明确见证，说明两态合法性接缝并不普遍限制相干秩。[^CE-S]

**经典混合与共同环境。** 同一全链经典律的对角态是


<table><tbody><tr><td>

```math
\rho_{\mathrm{diag}}=
\sum_{\text{合法 }b}\frac{\omega(b)}{\mathcal{\text{𝒵}}_N}
\bigl(|b_L\rangle\langle b_L|\otimes
|b_R\rangle\langle b_R|\bigr).
```

</td></tr></tbody></table>


每项是乘积基态投影，权非负和为一，故它在每个切口可分。相同对角律既可来自上述相干纯态，也可来自这个可分混合。

更具体地，若同一制备实际为
$`|\Omega\rangle=\sum_b\sqrt{p_b}|b\rangle\otimes|e_b\rangle`$，全部记录归一化，迹掉记录给


```math
(\rho_{\mathrm{sys}})_{bc}
=\sqrt{p_bp_c}\,\langle e_c|e_b\rangle.
```


相同记录向量保留指定正相位纯态；正交记录给 $`\rho_{\mathrm{diag}}`$；一般共同记录要求联合 Gram 正性，逐对可行不足以保证共同实现。[^CE-S][^CE-R] 如果还携带历史相关目标作用 $`U_b`$，其相位和目标记录也必须属于同一个等距准备，不能仍自动宣称系统处于定义 C-20.1 的纯态。

这里经典求和、量子部分迹、相干振幅求和是不同映射。仅环境上的迹保持操作不改变系统无条件约化态：对任意系统测试 $`A`$，其迹配对用环境伴随映射的 $`\Lambda^\dagger(I)=I`$ 即得。若环境会再次共同作用，应保留完整联合边界。已有同一环境 CNOT 例子给准确限制：系统控制、环境初态零，作用一次后系统退相干；同一 CNOT 再作用于原环境因 $`W^2=I`$ 恢复初始联合态，而两次各用新环境仍退相干。[^CE-S] 因此环境再接入、反馈、相干比较都需要其真实制备和操作合同。端点经典近独立不说明整链可分、所有切口无关系、环境未来不可见或设备总成本低。

## 21. 任意有限阶局部报告仍可漏掉整体关系

**定义 C-21.1（始终合法的有限子语言）。** $`L\ge1`$ 固定；二值 $`\epsilon_j=0,1`$ 分别输入空模式 $`0`$、中间模式 $`2`$。两者 $`x=y=0`$，任意接续都合法，每个真实共享接缝零。另供有限共同来源律


<table><tbody><tr><td>

```math
P_\theta(\epsilon)=2^{-L}[1+\theta(-1)^{\epsilon_1+\cdots+\epsilon_L}],
\qquad-1\le\theta\le1.
```

</td></tr></tbody></table>


本章参数 $`\theta`$ 是整体奇偶偏好，区别于单窗 $`\kappa`$、相位 $`\Phi`$ 及探针设置。

**命题 C-21.2（真子集报告相同、整体来源不同）。** $`P_\theta`$ 非负归一化，对每个真子集 $`A\subsetneq\{1,\ldots,L\}`$，$`P_\theta(\epsilon_A)=2^{-|A|}`$。$`\theta=1,-1`$ 分别支持偶、奇历史。因此任意固定阶局部报告不能认证任意更长整体，除非另外供应来源结构假设。

**证明。** 非负由 $`|\theta|\le1`$；总奇偶和 $`\prod_j\sum_{\epsilon_j}(-1)^{\epsilon_j}=0`$，故和一。真子集至少漏一位，在其求和中奇偶项抵消，包含空集和 $`L=1`$ 的情形。端点一类质量为 $`2^{1-L}`$、另一类零，支持不同。固定非零 $`\theta`$ 的各长度族不是自动一致的无限过程：长度 $`L+1`$ 的首 $`L`$ 位边缘是均匀 $`P_0`$，与非零参数长度 $`L`$ 不同。这是有限来源反例，不是无限过程存在性定理。$`\square`$

## 22. 同历史原生数量怎样读取高阶差分

**命题 C-22.1（权重与精确终值单射）。** 对 §21 同一历史，原生终值为


<table><tbody><tr><td>

```math
Q(\epsilon)=\sum_{j=1}^L w_j\epsilon_j,
\quad w_j=qS^{L-j}\beta=F_{3(L-j)+4},
\quad\beta=(0,1)^{\mathsf{\text{𝖳}}}.
```

</td></tr></tbody></table>


$`L=2`$ 权重 $`(13,3)`$，$`L=3`$ 为 $`(55,13,3)`$。每个权重超过其后全部权重和，因此固定 $`L`$ 的精确 $`Q`$ 单射地编码全部位。

**证明。** 对更新 $`C'=SC+\epsilon\beta`$ 展开 Horner 和得到组成；$`qM^n\beta`$ 的初值三、五及 $`M^2=M+I`$ 给 $`F_{n+4}`$。$`F_{n+3}=2F_{n+1}+F_n>2F_n`$ 对 $`n\ge4`$，故相邻降序权比大于二。其后尾和小于 $`w_{j+1}(1+1/2+1/4+\cdots)<2w_{j+1}<w_j`$。两位串首个不同位置的权重超过全部以后差值，终值不同；可贪心反解。单射要求实际取得足够精度的整数 $`Q`$ 和已知长度，低阶矩盲不扩大为所有读口盲。$`\square`$

**命题 C-22.2（首次非零多项式阶数与任意目标）。** 对 $`0\le k<L`$，$`\mathbb{\text{𝔼}}_\theta Q^k=\mathbb{\text{𝔼}}_0Q^k`$，而


<table><tbody><tr><td>

```math
\mathbb{\text{𝔼}}_\theta Q^L-\mathbb{\text{𝔼}}_0Q^L
=\frac{\theta(-1)^LL!}{2^L}\prod_jw_j.
```

</td></tr></tbody></table>


对实际有限和集上的任意实函数 $`f`$，若 $`\Delta_wf(t)=f(t+w)-f(t)`$，则


<table><tbody><tr><td>

```math
\mathbb{\text{𝔼}}_\theta f(Q)-\mathbb{\text{𝔼}}_0 f(Q)
=\frac{\theta(-1)^L}{2^L}\Delta_{w_1}\cdots\Delta_{w_L}f(0).
```

</td></tr></tbody></table>


若另有 $`f\in C^L([0,\sum w_j])`$，还可写


```math
\Delta_{w_1}\cdots\Delta_{w_L}f(0)=
\int_0^{w_1}\cdots\int_0^{w_L}
 f^{(L)}(t_1+\cdots+t_L)\,dt_1\cdots dt_L.
```


**证明。** 展开 $`Q^k`$，每个 $`k<L`$ 单项式至少漏一位，其奇偶加权求和为零。$`k=L`$ 唯一含全部位的项为 $`L!\prod w_j\epsilon_1\cdots\epsilon_L`$，在全一串上的符号 $`(-1)^L`$，给首式。交替角点求和的符号为 $`(-1)^{L-\sum\epsilon}`$，故一般期望差是 $`(-1)^L`$ 乘有限差分。最后一式对正权重逐次使用微积分基本定理，规定整个区间的连续 $`L`$ 阶导数；只在离散和集定义的 $`f`$ 无此积分义务。$`L=2`$ 四角差读取二重交叉，$`L=3`$ 八角差读取三重交叉，称面积／体积型只说明响应阶数，未声明实际物理空间维数。$`\square`$

## 23. 有限奇偶任务的因果边界与真实成本

**定义 C-23.1（来源生成与允许原生推进）。** 给定有限 $`L,\theta`$ 和实际输入资源，来源生成器按 §21 供应逐窗 $`\epsilon`$，观察者只能累计实际返回输入，不能任意挑选结果。阶段 $`j`$ 的边界保留来源标识、$`(j,L,\theta)`$、真实 $`s=0,C_j`$、输入／精度／资源档案；可缓存奇偶 $`\varrho_j=\sum_{i\le j}\epsilon_i\pmod2`$。$`j<L`$ 且输入资源存在时允许下一推进，$`j=L`$ 完成本合同。该完成不是增加原生 Stop、End 或重置。

**命题 C-23.2（有限源的真实条件分支）。** 任何正质量 $`j<L`$ 前缀的概率为 $`2^{-j}`$。剩 $`m=L-j\ge1`$ 位的条件律为


<table><tbody><tr><td>

```math
P_\theta(\epsilon_{j+1:L}\mid h_j)
=2^{-m}[1+\theta(-1)^{\varrho_j+\sum\epsilon_{j+1:L}}].
```

</td></tr></tbody></table>


$`j<L-1`$ 的下一位公平；$`j=L-1`$ 时


<table><tbody><tr><td>

```math
P_\theta(u\mid h_j)=\tfrac12[1+\theta(-1)^{\varrho_j\oplus u}],
\quad C_{j+1}=SC_j+u\beta,
\quad\varrho_{j+1}=\varrho_j\oplus u.
```

</td></tr></tbody></table>


这些数据对本合同的全部有限历史和回复律充分。

**证明。** 对至少一剩余位求和消掉奇偶项，前缀质量 $`2^{-j}`$；将全历史概率除以它给条件式。若还剩至少两位，对其余位求和得下一位 $`1/2`$；仅最后一位时式不再消掉。所有守卫因 $`x=y=0`$ 通过，数量后继是原生实际更新，公开阶段和资源同步扣除。若 $`\theta=\pm1`$ 最后某支零质量，就没有该支后验；正完成支按实际概率条件化。归纳连乘这些因果核得到正前缀公平概率及最终全历史 $`P_\theta`$，再把同数量历史求和给回复律。相同边界给相同资源菜单、输入分支、数量后继和阶段更新，因而任意该有限合同策略的历史律下降。加权生成函数不是这份条件核的替代物。$`\square`$

**命题 C-23.3（奇偶缓存未必增加信息）。** 在此中间／空子语言中


<table><tbody><tr><td>

```math
\varrho_j=(C_j)_2\bmod2=Q_j\bmod2.
```

</td></tr></tbody></table>


因此已有精确组成或数量记录时，奇偶缓存不构成必要新增信息位。只保留几何接缝零时却不能恢复它。

**证明。** $`S\bmod2=I`$，每次 $`u\beta`$ 把第二组成分量奇偶翻 $`u`$；初值全零，归纳得第一式。$`q\bmod2=(0,1)`$ 给第二式。同接缝的不同正前缀可以有相反奇偶，最后条件核遂不同。可缓存一位是计算表示选择，不是装置总状态一位或在线最小性。窗口位置、$`L,\theta`$ 描述、精确整数位宽、实际输入和输出仍付成本；数值 $`C_j`$ 的表示不能当作常数空间。针对完整历史恢复的成本又不同。$`\square`$

**命题 C-23.4（同历史生成多项式与方向约定）。** 以行向量状态记录偶、奇，形式变量 $`t`$ 下


```math
T_j(t)=\begin{pmatrix}1&t^{w_j}\\t^{w_j}&1\end{pmatrix},
```


<table><tbody><tr><td>

```math
\mathcal{\text{𝒢}}_\theta(t)=2^{-L}(1,0)
T_1(t)\cdots T_L(t)\binom{1+\theta}{1-\theta}
=2^{-L}\left[\prod_j(1+t^{w_j})+
\theta\prod_j(1-t^{w_j})\right].
```

</td></tr></tbody></table>


**证明。** 输入零保持奇偶权一，输入一翻转且乘 $`t^{w_j}`$，故矩阵从旧行到新列；末向量按最终奇偶赋 $`1\pm\theta`$，恰恢复所有同历史权。共同特征行 $`(1,1),(1,-1)`$ 的特征值 $`1+t^{w_j},1-t^{w_j}`$，分解初行得乘积式。$`T_j`$ 是形式加权转移，不是行和一的随机核，亦不授予自由控制来源。计算全部系数或完整分布须另付其输出、算术和精度成本，不用一奇偶寄存器大小掩盖输出规模。$`\square`$

**命题 C-23.5（未知参数和更大共同环境仍有不同义务）。** 正真前缀对未知 $`\theta`$ 的似然恒定，未取得完整奇偶前不能据此学到 $`\theta`$；完成奇偶的似然因子为 $`1+\theta(-1)^{\varrho_L}`$。另供相干历史实现时，经典奇偶不一般充分。

**证明。** 第一结论由 $`P(h_j)=2^{-j}`$，完整记录条件于参数的 $`2^{-L}`$ 常数消去后给所列因子；若另供先验且证据正，用该因子作 Bayes 更新，零证据支无后验。相干模型 [C-R4] §110 另供共同环境上的等距


```math
V_n=\sum_{h,a}|h,a\rangle\langle h|\otimes K_{a|h},
\quad\sum_aK_{a|h}^\dagger K_{a|h}=I,
\quad\Omega_n=\sum_{h,k}|h\rangle\langle k|\otimes\Xi^{(n)}_{hk}\succeq0.
```


于是


<table><tbody><tr><td>

```math
\Xi^{(n+1)}_{ha,kb}=K_{a|h}\Xi^{(n)}_{hk}K_{b|k}^\dagger.
```

</td></tr></tbody></table>


输出历史基正交给 $`V_n^\dagger V_n=I`$，展开共轭得式，正性和迹一保持；对角块迹才是经典概率。若分支有隐藏 Kraus 指标，须保留给定环境或扩展指标，不从抽象分支名自由选择交叉相位。具体地系统控制同一环境量子位的 CNOT 一次把 $`|+\rangle|0\rangle`$ 送到 Bell 态，忽略环境给 $`I/2`$；第二次同一 CNOT 因平方恒等恢复 $`|+\rangle`$，两次改用新环境则仍 $`I/2`$。因此同局部边缘、同经典概率不决定共同未来，且没有证明经典奇偶压缩上述 $`\Xi`$。$`\square`$

## 24. 所有关系层的任务下降与来源接口

**接口 C-24.1（指定任务的充分边界）。** 实际状态与来源标识、档案、资源和阶段使用 [A 卷 §19](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#19-算术精度未来深度与任务充分边界) 命题A-19.4的完整确定／随机下降条件：公开菜单、enabled、各回复和失败类型、费用及后继摘要的联合核须在实际非空纤维上相同。

**接口 C-24.2（有限未来的任务范围）。** 同一摘要策略的完整有限历史律下降，证明见 [A 卷 §19](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md#19-算术精度未来深度与任务充分边界)；秩、当前均值或静态极值不能替代联合核。体积、同概率异相位、同边缘异联合和共同环境反例分别检验不同合同的遗漏。下表列出每层实际恢复的对象。

| 关系层与供给 | 可恢复的边界 | 仍须保留的限制与实际消费者 |
| --- | --- | --- |
| 五态均值 $`(X,Y,Z)`$ | 一条闭概率纤维 | $`J_f\omega=0`$ 才识别期望；奇数档案继续一般需 $`\kappa`$ |
| 完整 $`p`$／四个可行精确矩 | 全部单窗经典函数律 | 实际阶段与同源档案；不能推出任意跨窗耦合 |
| 固定律残差 $`h`$、信息 $`\mathcal{\text{ℐ}}`$ | 函数投影与实验局部敏感度 | 支撑、参数单位与真实读口 $`W`$；不是未知律取得 |
| 协方差秩、$`D`$、四 IID 平方体积律 | 波动维数与无符号体积任务 | §6 的残差符号可仍改变拒绝率；完整 $`C`$ 更强 |
| 共同参考及 Gram 条目 | 可实现圆盘／Schur 剩余秩 | 同一载体、零主元、实际关系取得；不是布尔合法性 |
| 三角 Bargmann 与接缝重叠 | 非零接缝下的外圈恢复 | 正交接缝可使该剖分不可逆；实验资源另供 |
| 整数来源加中心位 | 声明 Pauli 表示及相对符号 | 原树叶序、括号与相干比较合同仍分开 |
| 纯五態 $`p,\chi`$ 加位置标架 | 固定均值的关系商坐标 | 顶点／侧面／锥端；pair 后选择和记录 $`\eta_{\rm rec}`$ |
| 双窗完整边缘 | 接缝可行三角与运输纤维 | 十二或四维只在相应正支撑；$`E_{\rm adm}`$ 决定全纤维 |
| 合法二部 $`p,\Phi_{ij}`$ | 局部模式相位商及循环任务 | 全非零锚、两份比较失败、真实记录、支撑纠缠 |
| 有限奇偶源与精确 $`(j,C_j)`$ | 指定有限原生预测及生成式 | 奇偶缓存冗余于精确 $`Q`$；非零参数不自动无限一致 |
| 相干历史块与共同未来环境 | 所供等距合同内的未来联合律 | 不能由经典概率或奇偶直接压缩 |

表中恢复均是有前提的数学映射；存在、可识别、实际取得、认证是不同命题。$`\square`$


**命题 C-24.3（已取得前缀的补充记录不免费提供未知律）。** [C-R7] §§18–23 的实际前缀构造可作为这里“来源标识—档案—资源”接口的实例，但不给本卷未知 $`p`$、Gram 条目或相干参考。

**证明。** 该原始解析器从真实返回字母更新准确计数和有限标签，字典大小 $`G_\kappa(A,B)`$ 由已声明文法计算；最后边的前驱块按固定顺序排列，实际秩更新为旧秩加所有先行块的大小。各块唯一分割当前字典，归纳给实际前缀与 $`0,\ldots,G_\kappa-1`$ 的双射，逆操作每步减少已取得字母数，未查询丢弃过去。秩／计数事务在指定第三锁存前完成，此后保持同一记录；原第四阶段、停止与外承诺行为不改。相对给定边界的数据字母表 $`G_\kappa`$、固定纤维位数 $`\lceil\log_2G_\kappa\rceil`$、计数元数据、算术工作空间、安装、保持、交付与物化输出均是分别收费的对象。字典存在不等于字母已取得，逆式存在不等于免费交付整个历史。其二阶有序计数还另供实际更新和更大计算界；不能把它当作本卷四个总体矩已得。故该实例只支持因果取得的接口纪律，不提供未知概率或免费实验，也不把原生生成步数、静态图边或归档顺序当作物理时间。$`\square`$

**命题 C-24.4（单窗、接缝与高阶关系的三个统一桥）。** 在各自指定任务合同中，以下三式分别连接共享部分与后继、局部循环与联合恢复、关系阶数与目标响应：


<table><tbody><tr><td>

```math
\langle x-Xb/r,y-Yb/r\rangle=\Delta/r
=m(g-g_*),
\qquad D=D_*-Zrm^2(g-g_*)^2.
```

</td></tr></tbody></table>


<table><tbody><tr><td>

```math
p'-p=\sum_{i,j\ne0,(i,j)\in E}(p'_{ij}-p_{ij})D^{ij},\qquad
\chi_{ij}=\frac{c_{ij}c_{00}}{c_{i0}c_{0j}},\qquad
 ds^2=\tfrac14dt^{\mathsf{\text{𝖳}}}\mathscr{\text{ℐ}} dt+d\Phi^{\mathsf{\text{𝖳}}}\mathscr{\text{ℐ}}^{-1}d\Phi.
```

</td></tr></tbody></table>


<table><tbody><tr><td>

```math
\mathbb{\text{𝔼}}_\theta f(Q)-\mathbb{\text{𝔼}}_0f(Q)
=\frac{\theta(-1)^L}{2^L}\Delta_{w_1}\cdots\Delta_{w_L}f(0),
\qquad \varrho_j=Q_j\bmod2.
```

</td></tr></tbody></table>


**证明。** 第一式是命题 C-3.2、C-6.2；第二组是命题 C-17.2、C-18.2、C-18.4；第三组是命题 C-22.2、C-23.3。每式保留其正分母、实际支持和供给合同。函数的共同项、概率的隐藏方向、相位的闭路以及任务的充分未来边界可相互桥接，却未合并为同一物理对象；已由参考解释的关系可以消元，恢复需要的接缝权重、来源和费用仍保留。$`\square`$

**命题 C-24.5（内部消元与共同来源的六桥）。** 以下六式各保留自己的域：


<table><tbody><tr><td>

```math
xz=zy=0
```

</td></tr></tbody></table>


固定五模式合法来源；


<table><tbody><tr><td>

```math
W(x,y)=\sum_z a^xb^zc^y\mathbf{\text{𝟏}}_{\{xz=zy=0\}}
```

</td></tr></tbody></table>


把同一中位的全部可能收进实际端点；


<table><tbody><tr><td>

```math
\det W=abc
```

</td></tr></tbody></table>


保存正活动中位留下的端点关联；


<table><tbody><tr><td>

```math
\det W_N=(-1)^{N-1}\prod_iw_i
```

</td></tr></tbody></table>


在因子化路径中传播有向响应，$`N=1`$ 按同位联合定义；


<table><tbody><tr><td>

```math
w_i=1,\ N\ge2:\quad
\operatorname{Cov}(b_1,b_N)=\frac{(-1)^{N-1}}{F_{N+2}^2}
```

</td></tr></tbody></table>


把精确端点关系连接到合法计数和有限端点误差；


<table><tbody><tr><td>

```math
\log\left(1+b\prod_i(1-x_i)\right)
=\log(1+b)\prod_i(1-x_i)
```

</td></tr></tbody></table>


在另供 Boolean 星形协议中显示受同一参数约束的高阶因子。

实际 FIB 消费链还包括


<table><tbody><tr><td>

```math
P\longmapstop_2=\frac{\det P}{P_{11}}
\longmapsto\Pr(R=18\mid00)=\frac{\det P}{P_{00}P_{11}},
```

</td></tr></tbody></table>


以及完整原生窗的首高位／下一守卫联合事件误差
$`(-1)^{3L-1}/F_{3L+2}^2`$。前者依赖已知模型、精确端点律和实际档案；后者依赖单位活动完整路径与有限端点任务。它们把所用概率、转移、消元和信息工具接回同一来源的允许回复。

| 结构 | 数学作用与保留范围 |
| --- | --- |
| 点式二值记录 | 一个位置当前是否占用，区别于组成数量 |
| 排斥边 | 禁止相邻占位 $`11`$，本身不指定概率 |
| 三位置五模式 | 两条排斥经同一中位生成端点联合因子 |
| 正方形端点概率表 | 保存四端点概率和行列式；内部拆分依赖来源模型 |
| 长链 | 在同源因子化条件下传播符号并改变归一化尺度 |
| 高阶边界因子 | 原共同中心消元后的唯一 Boolean 展开，系数由同一 $`b`$ 约束 |
| 小型动态边界 | 保留指定回复所需共同状态；一般数量未来还须组成／条件律及记录资源 |

一个看似新增的关系，究竟是独立自由度，还是同一个隐藏来源在另一张边界上的表达？在此模型中，端点行列式、四角系数和星形高阶项都有可计算的共同来源。改用完整边界表达可保留指定响应；若删除允许下一回复仍能区分的组成、相位或共同环境，就有实质信息损失。判断依据是声明的来源与完整任务合同。

## 25. 数学引文及直接使用范围

**约定 C-25.1（不可变仓库来源）。** 下列链接均指完整提交，章节号属于各原文；[C-R1]–[C-R7] 是 `repo-derived` 来源及其明确引用的成熟理论。五组关系的原来源快照包括 `3a888f3560ee2dcfa9c4109236e60db93b3d48fb`、`9898c68d2fa7ade71e7035b7faa2ef5ae708949f`、`4c02a48d490528e6637c42f280e4d5972a2d3243`、`aed0cc25936de32be5145201bb7f19f64a0ed84d`、`3655cb5f3ef29875a414497a6262b818121e8819`；正文使用下列实际共同接口，不借未提供附件或活动草稿。

| 来源 | 原文与版本 | 本卷直接消费范围 |
| --- | --- | --- |
| [C-R1] | [《FIB 关系延拓几何》](https://github.com/the-omega-institute/trureturing/blob/aed0cc25936de32be5145201bb7f19f64a0ed84d/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) | 定义 1.1–1.3、§3、定义 7.1 与定理 7.2–7.3；原树、组成、原生方向、守卫和空窗 |
| [C-R2] | [《金字塔：关联纤维与原生接续》](https://github.com/the-omega-institute/trureturing/blob/aed0cc25936de32be5145201bb7f19f64a0ed84d/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md) | §§3–4、定义 8.1、命题 8.7–8.10；概率纤维与同源双窗数量任务 |
| [C-R3] | [《金字塔基础公式、原子关系与同源接续总表》](https://github.com/the-omega-institute/trureturing/blob/aed0cc25936de32be5145201bb7f19f64a0ed84d/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) | §§1–7、9、§§11.6–11.11；完整函数、最大熵、真实奇偶档案后继续 |
| [C-R4] | [《二阶关系完成》](https://github.com/the-omega-institute/trureturing/blob/aed0cc25936de32be5145201bb7f19f64a0ed84d/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) | §§39、53、101–110；既有函数／回路、整数中心符号、同组成比较、共同记录与相干历史 |
| [C-R5] | [《金字塔行列式与原生守卫续接》](https://github.com/the-omega-institute/trureturing/blob/3a888f3560ee2dcfa9c4109236e60db93b3d48fb/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md) | §§4–5、9–10；$`\Delta`$、闭域補全及 initialized 奇偶消费者 |
| [C-R6] | [《局部选择几何》](https://github.com/the-omega-institute/trureturing/blob/aed0cc25936de32be5145201bb7f19f64a0ed84d/docs/develop/theory/FIB_ATOM_LOCAL_CHOICE_GEOMETRY.md) | §§7、9；共同记录相位、带菜单与失败的任务下降 |
| [C-R7] | [《递归关系观察、空间记录与时序》](https://github.com/the-omega-institute/trureturing/blob/3a888f3560ee2dcfa9c4109236e60db93b3d48fb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md) | §§18–23；实际前缀取得、保持、交付及独立资源坐标；不免费取得本卷未知律 |

**约定 C-25.2（文献中的中间步骤）。** 以下均 `literature-attested`，只承担表中中间结果；各有限 FIB 域的支撑分类、反演、任务桥和条件响应由前述普通证明给出，不主张全局原创性。

| 来源 | 完整题名、版本与链接 | 精确使用范围 |
| --- | --- | --- |
| [C-L1] | Stephen Boyd、Lieven Vandenberghe，[*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)，2004 年书，作者站修正印刷版，附录 A.5.5，印刷页 650–651 | Schur 补、奇异参考 range 条件；本卷实际投影与递归在 §9 自证 |
| [C-L2] | Frank Nielsen，[*An elementary introduction to information geometry*](https://arxiv.org/abs/1808.08271v2)，v2；同题扩展出版 [Entropy 22(10), 1100 (2020)](https://doi.org/10.3390/e22101100) | Fisher–Rao、得分、平方根概率嵌入的经典背景；两版本不当作独立证据；§4 的有限信息损失自证 |
| [C-L3] | Michał Oszmaniec、Daniel J. Brod、Ernesto F. Galvão，[*Measuring relational information between quantum states, and applications*](https://arxiv.org/abs/2109.10006v1)，v1，式 (1) 与 Fig. 1 的 cycle tests | Bargmann 闭路及额外受控循环制备背景；不冒称该文证明本卷五态四角投影概率 |
| [C-L4] | William K. Wootters，[*Entanglement of Formation of an Arbitrary State of Two Qubits*](https://arxiv.org/abs/quant-ph/9709029v2)，v2，式 (4)、(7) | 纯态 spin-flip concurrence；§12 明确计算 $`2\lvert\det\mathcal{\text{𝒜}}\rvert`$，不调用未供给混态任务 |
| [C-L5] | Abhay Ashtekar、Troy A. Schilling，[*Geometrical Formulation of Quantum Mechanics*](https://arxiv.org/abs/gr-qc/9706069v1)，v1，§II | 射线空间度量背景；本文 FS 归一化另定，不移植其物理尺度或声明全局 toric 对应 |
| [C-L6] | Jesús A. De Loera、Edward D. Kim，[*Combinatorics and Geometry of Transportation Polytopes: An Update*](https://arxiv.org/abs/1307.0124v1)，v1，§2 | 行列边缘与运输多面体背景；其无禁止格一般结果不替代 §17 全纤维可用支持计算 |

[^CE-C]: 《Auric FIB ATOM 金字塔：关联纤维与原生接续》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)，定义 1.1、6.3，推导 6.4，定义 8.1–8.2、推导 8.3–8.5、命题 8.7–8.9。消费位置字典、额外相干合同、两读向核、整源因子化与相关历史反例。
[^CE-D]: 《Auric FIB ATOM 金字塔续篇：行列式、条件拼接与原生守卫接续》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)，推导 4.2–4.3、5.1–5.2、6.1–6.3、7.1，约定 7.2，定义 10.4、命题 10.5–10.7。消费底面行列式与总体协方差区别、正活动条件以及真实档案后继续任务。
[^CE-F]: 《FIB-ATOM 金字塔：基础公式、原子关系与同源接续总表》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，§9.1，定义 11.1–11.3、命题 11.4–11.5、定义 11.6、数学引文 11.7、命题 11.8–11.9、边界 11.11、§12.5。消费概率核的绝对质量、缺失拆分、下一回复表与取得边界。
[^CE-G]: 《FIB 关系延拓几何》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)，定义 3.2–3.3、5.1–5.2、定理 5.3–5.4、定义 7.1、定理 7.2–7.3。消费完整菜单的动态纤维判据、同源权重保持收缩、真实高到低读者和整词方向桥。
[^CE-S]: 《Auric · FIB-ATOM 续篇：二元来源的三维二阶关系完成》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)，定义 71.1、定理 71.2–71.3，§§107–108、命题 109.3、定义 110.1、定理 110.2、命题 110.3–110.4。消费 Schmidt/SVD、指定等振幅上界、任意支撑振幅的反例及共同制备、记录和可复用环境条件。
[^CE-R]: 《Auric：FIB-ATOM 续篇——差异边界、记录几何与时间箭头》，[固定提交正文](https://github.com/the-omega-institute/trureturing/blob/3655cb5f3ef29875a414497a6262b818121e8819/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)，定义 125.1、定理 125.2–125.3、假设 125.4–125.5。消费同一有限实现中的权重、具体作用和共同记录分离，及数学兼容性与实际取得的区别。
[^CE-HC]: Alistair Sinclair、Piyush Srivastava、Yitong Yin，*Spatial mixing and approximation algorithms for graphs with bounded connective constant*，[arXiv:1308.1762v2](https://arxiv.org/abs/1308.1762v2)，§1.1。只消费统一活动硬核独立集模型定义；其 Theorem 1.1 要求统一活动 $`\lambda<\lambda_c(\Delta+1)`$ 及连接常数至多 $`\Delta`$ 的图族，此处不调用该强空间混合结论。
[^CE-VE]: Nathalie Peyrard、Marie-Josée Cros、Simon de Givry、Alain Franc、Stéphane Robin、Régis Sabbadin、Thomas Schiex、Matthieu Vignes，[arXiv:1506.08544v2](https://arxiv.org/abs/1506.08544v2)，§§2.1–2.2、3.2。摘要页题名为 *Exact and approximate inference in graphical models: variable elimination and beyond*；v2 PDF 题名为 *Exact or approximate inference in graphical models: why the choice is dictated by the treewidth, and how variable elimination can be exploited*，是同一版本记录。消费有限因子化、分配律及消元生成邻域因子的步骤，不调用一般图宽度最优性或稠密表成本作为此特殊秩二表示的下界。

## 追加锚（本行以下为增补区）

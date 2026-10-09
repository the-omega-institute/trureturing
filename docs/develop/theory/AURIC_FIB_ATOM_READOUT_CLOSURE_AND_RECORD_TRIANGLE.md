# Auric FIB-ATOM：读口的完整分类与记录三角形

从正方形关联，到二结果限制、三结果完成与记录粗化。

**来源与证据边界。** 来源是用户在本次会话供应的同名理论文本，原文固定读取快照 `ef02f0d`，引用 #14790 和 #14792。交付类型为 mixed：用户供应原文，Codex 做标题和数学分隔符整理；原作者姓名及原模型未提供。来源接收日期为 2026-10-09。本文是参考输入，Lean 声明与证明才是仓库数学真值来源。下列 `Claim status: open` 表示本卷没有为这些条目供应 Lean 证明，不否定原文中的普通数学论证。原文实验计数仅作为作者报告保留；本次摄入未取得相应脚本和结果文件，未复跑那些实验。

## 0. 任务与最小记录结构

什么样的读口，能够在每一种实际结果出现后，都保持原来的简单来源结构？

只有两个结果的读口，不能同时读取两个独立端点的信息，又要求每个后验都不产生端点关联。这里“读取两个端点的信息”严格指：在底面条件下，两个端点的后验均值都随记录结果发生变化。三个结果可以做到，而且三个恰好是最少的。这三个结果产生的后验均值能够形成一个有非零面积的三角形。

因此，三角形在这一层的语义是承载两项非零、彼此正交的信息变化所需的最小记录结构。这不是从三种记录推出三维物理空间，而是从观察、条件独立与概率守恒推导出的最小结构。

## 1. 要保持的简单来源结构

继续使用五模式：

$$
\Sigma=\{\mathsf F[\varnothing],\mathsf F[1],\mathsf F[2],\mathsf F[3],\mathsf F[1,3]\}.
$$

低端、高端、中间占位分别为

$$
x=\mathbf1_{\{1\text{ 被选}\}},\qquad
y=\mathbf1_{\{3\text{ 被选}\}},\qquad
z=\mathbf1_{\{2\text{ 被选}\}},\qquad xz=yz=0.
$$

概率次序为 $p=(p_{\varnothing},p_1,p_2,p_3,p_{13})$。一般五模式律有四个独立参数。三个均值 $X=\mathbb E[x]$、$Y=\mathbb E[y]$、$Z=\mathbb E[z]$ 之外，还需要 $\kappa=\mathbb E[xy]$。

另外声明乘积活动权模型

$$
\mathfrak M=\left\{p=\frac{(1,a,b,c,ac)}{1+a+b+c+ac}:a,b,c>0\right\}.
$$

后者只有三个参数，但它不是由合法性自动推出的。

### lemma 1: 乘积活动权模型的精确关系方程

**Claim status: open.** 对严格正的五模式概率，

$$
p\in\mathfrak M\iff\Delta(p):=p_{\varnothing}p_{13}-p_1p_3=0,
\qquad \Delta=(1-Z)\kappa-XY.
$$

证明。乘积权直接给出四角等式。反过来，令 $a=p_1/p_{\varnothing}$、$b=p_2/p_{\varnothing}$、$c=p_3/p_{\varnothing}$，四角等式保证 $p_{13}/p_{\varnothing}=ac$。第二式由概率恢复式展开。证毕。

在条件 $z=0$ 下，这正是 $x$ 与 $y$ 独立。本篇分类的是哪些观察能够保持这份明确的三参数来源模型，而不是禁止一切关联。

## 2. 全部结果同时保持模型族

### 定义 1：二结果条件读口

假设本次操作不改变真实模式，只返回记录 $O\in\{0,1\}$。记

$$
\lambda_s=\Pr(O=1\mid s),\qquad 0<\lambda_s<1.
$$

另一结果的似然必须为 $1-\lambda_s$。结果后验为

$$
p_s^{\,1}=\frac{p_s\lambda_s}{\sum_t p_t\lambda_t},\qquad
p_s^{\,0}=\frac{p_s(1-\lambda_s)}{\sum_t p_t(1-\lambda_t)}.
$$

称读口保持模型族，如果对每份 $p\in\mathfrak M$，两个后验都仍属于 $\mathfrak M$。严格正条件排除了零概率与支持改变的特殊情形；确定性极限须单独处理，不能直接套用含除法的证明。

### theorem 1: 二结果读口保持五模式乘积族的完整分类

**Claim status: open.** 该读口保持 $\mathfrak M$，当且仅当属于以下两类之一：

$$
\lambda_s=\lambda_{\varnothing}+(\lambda_1-\lambda_{\varnothing})x(s)+(\lambda_2-\lambda_{\varnothing})z(s),
$$

或者

$$
\lambda_s=\lambda_{\varnothing}+(\lambda_3-\lambda_{\varnothing})y(s)+(\lambda_2-\lambda_{\varnothing})z(s).
$$

换句话说，读口只能直接依赖低端加中间，或高端加中间，不能同时对底面上两个可独立占用的端点作非平凡读取。

证明。结果一保持独立要求

$$
\lambda_{\varnothing}\lambda_{13}=\lambda_1\lambda_3.\tag{1}
$$

结果零保持独立要求

$$
(1-\lambda_{\varnothing})(1-\lambda_{13})=(1-\lambda_1)(1-\lambda_3).\tag{2}
$$

两式相减得到 $\lambda_{\varnothing}+\lambda_{13}=\lambda_1+\lambda_3$，代回 (1) 得

$$
(\lambda_1-\lambda_{\varnothing})(\lambda_3-\lambda_{\varnothing})=0.
$$

所以至少有一端的似然变化为零。若 $\lambda_3=\lambda_{\varnothing}$，则 $\lambda_{13}=\lambda_1$，得到第一类；若 $\lambda_1=\lambda_{\varnothing}$，则 $\lambda_{13}=\lambda_3$，得到第二类。中间模式似然 $\lambda_2$ 不参与底面四角关系，可以独立指定。反向逐项代入即可。证毕。

低端与中间的合法联合状态只有 $(0,0),(1,0),(0,1)$，形成三角形；高端与中间同样如此。二结果读口若要求任何结果都不引入端点关联，就必须退回其中一张三角关系结构。该结论依赖静态来源只读、两个结果、每个结果保持指定乘积族，不是普遍的观察二选一定律。

## 3. 独立关系的马鞍面

条件于底面 $z=0$，令 $u=\Pr(x=1\mid z=0)$、$v=\Pr(y=1\mid z=0)$、$k=\Pr(x=y=1\mid z=0)$。条件独立为 $k=uv$，在 $(u,v,k)$ 坐标中是一张马鞍型曲面。

### theorem 2: 混合独立来源的新增关联

**Claim status: open.** 两份独立来源端点均值为 $(u_0,v_0)$、$(u_1,v_1)$，按权重 $1-t,t$ 混合，则

$$
\begin{aligned}
\bar u&=(1-t)u_0+tu_1,\\
\bar v&=(1-t)v_0+tv_1,\\
\bar k&=(1-t)u_0v_0+tu_1v_1,\\
\bar k-\bar u\bar v&=t(1-t)(u_1-u_0)(v_1-v_0).
\end{aligned}
$$

证明。展开并整理。$(u_1-u_0)(v_1-v_0)$ 是两坐标方向围成的带符号矩形面积。两个均值同向改变产生正关联，反向改变产生负关联，至少一个均值不变则仍独立。证毕。

二结果观察满足 $p=\Pr(O=0)p^{\,0}+\Pr(O=1)p^{\,1}$。若原来源和两个后验都独立，这条连接后验的线段经过独立曲面上的原点，由公式可知至少有一个端点均值相同。二结果只产生一条记录分离线；留在独立曲面上的这条线必须沿一个端点不变的方向。

## 4. 三结果完成与最小性

### 定义 2：三结果五模式读口

令 $O\in\{0,1,2\}$，条件概率表为

| 真实模式 | $O=0$ | $O=1$ | $O=2$ |
| --- | ---: | ---: | ---: |
| $\mathsf F[\varnothing]$ | $1/3$ | $5/9$ | $1/9$ |
| $\mathsf F[1]$ | $1/9$ | $5/9$ | $1/3$ |
| $\mathsf F[2]$ | $1/3$ | $1/3$ | $1/3$ |
| $\mathsf F[3]$ | $2/3$ | $1/9$ | $2/9$ |
| $\mathsf F[1,3]$ | $2/9$ | $1/9$ | $2/3$ |

每行和为一，所有概率严格正。

### theorem 3: 三结果读口对全部乘积活动权来源保持模型族

**Claim status: open.** 对上表每个结果 $o$，都有

$$
\lambda_{\varnothing,o}\lambda_{13,o}=\lambda_{1,o}\lambda_{3,o}.
$$

故每份 $p\in\mathfrak M$ 的三个后验都仍属于 $\mathfrak M$。

证明。逐列相乘验证四角等式，使用引理 1。证毕。

取五模式均匀先验 $p_s=1/5$。三个结果各以 $1/3$ 概率发生，且每个后验都有 $Z_o=1/5$。底面条件下后验均值为

| 结果 | $u_o=\Pr(x=1\mid o,z=0)$ | $v_o=\Pr(y=1\mid o,z=0)$ |
| --- | ---: | ---: |
| $0$ | $1/4$ | $2/3$ |
| $1$ | $1/2$ | $1/6$ |
| $2$ | $3/4$ | $2/3$ |

两个端点均值都随记录变化，每个后验仍条件独立。

### theorem 4: 三是实现该读取任务的最少结果数

**Claim status: open.** 要求底面原来源独立、每个正概率记录后仍独立、两个端点后验均值都不是记录上的常量，则至少需要三个结果；上表达到下界。

证明。在底面条件概率律下，总协方差给出 $0=\operatorname{Cov}(x,y)=\operatorname{Cov}_O(u_O,v_O)$。若只有两个正概率结果，中心化记录函数空间只有一维，两个非零中心化函数不能正交。显式地

$$
\operatorname{Cov}_O(u_O,v_O)=q_0q_1(u_1-u_0)(v_1-v_0),
$$

为零必使至少一个均值不变。三结果构造满足全部条件。证毕。

三个记录结果提供二维中心化关系空间，第一次容纳两项非零而正交的变化。

## 5. 记录三角形的精确面积

对上述例子，$\mathbb E_O[u_O]=\mathbb E_O[v_O]=1/2$，且

$$
\operatorname{Var}_O(u_O)=\frac1{24},\quad
\operatorname{Var}_O(v_O)=\frac1{18},\quad
\operatorname{Cov}_O(u_O,v_O)=0.
$$

记录 Gram 矩阵和行列式为

$$
G_{\mathrm{rec}}=\begin{pmatrix}1/24&0\\0&1/18\end{pmatrix},\qquad
\det G_{\mathrm{rec}}=\frac1{432}.
$$

三个后验点 $(1/4,2/3),(1/2,1/6),(3/4,2/3)$ 围成面积 $A_{\mathrm{rec}}=1/8$ 的三角形。

### theorem 5: 等权平面三记录的协方差行列式与面积

**Claim status: open.** 三个等权平面记录满足

$$
\det\operatorname{Cov}(v_O)=\frac4{27}A_\triangle^2.
$$

证明。以第一点为参考，设其余差向量为 $a,b$，$B=(a,b)$。三点均匀协方差为

$$
B\begin{pmatrix}2/9&-1/9\\-1/9&2/9\end{pmatrix}B^{\mathsf T}.
$$

中间矩阵行列式为 $1/27$，而 $(\det B)^2=4A_\triangle^2$。证毕。

原金字塔坐标有 $X_o=4u_o/5$、$Y_o=4v_o/5$、$Z_o=1/5$，所以

$$
A_{\mathcal P}=(4/5)^2(1/8)=\frac2{25}.
$$

面积量化后验均值在两个响应方向的非退化分离，不是物理空间中一次观测开辟的面积。

## 6. 粗记录重新产生关联

### 定义 3：细记录与粗记录

完整记录为 $T$，只保留 $C=g(T)$。在底面条件下假设每个细记录后验端点独立，记 $u_t=\mathbb E[x\mid T=t,z=0]$、$v_t=\mathbb E[y\mid T=t,z=0]$。

### theorem 6: 粗化后的关联等于细记录均值的协方差

**Claim status: open.**

$$
\operatorname{Cov}(x,y\mid C,z=0)=\operatorname{Cov}(u_T,v_T\mid C,z=0).
$$

证明。条件总协方差公式中，$\mathbb E[\operatorname{Cov}(x,y\mid T,z=0)\mid C,z=0]$ 因每个细后验独立而为零，余项正是右侧。证毕。

上例合并结果 $0$ 与 $2$ 后仍独立，因为 $v_0=v_2=2/3$；代价是丢掉二者低端差异的信息。合并结果 $0$ 与 $1$，二者等权，产生

$$
\operatorname{Cov}(x,y\mid C=\{0,1\},z=0)
=\frac14\left(\frac12-\frac14\right)\left(\frac16-\frac23\right)=-\frac1{32}.
$$

每个细记录是简单乘积来源，合并后却必须保留联合参数。少记一点可能把记录区别转成来源关联；它不意味着遗忘对实际来源施加了新作用力。

## 7. 任意有限排斥图的读口分类

### 定义 4：图上的乘积活动权来源

有限简单图 $G=(V,E)$ 的边表示不能共同占位，合法配置为独立集 $\Sigma_G$。定义

$$
P_w(I)=\frac1{Z(w)}\prod_{i\in I}w_i,\quad w_i>0,
\qquad \ell(I)=\Pr(O=1\mid I),\quad0<\ell(I)<1.
$$

### theorem 7: 二结果读口保持整个乘积族的排斥团分类

**Claim status: open.** 二结果读口保持整个乘积活动权族，当且仅当存在两两相邻的顶点集合 $C$（可为空或单点），使

$$
\ell(I)=\ell(\varnothing)+\sum_{i\in I\cap C}[\ell(\{i\})-\ell(\varnothing)].
$$

合法配置至多包含团中的一个位置。

证明。结果一保持乘积族时，比较空配置和单位置配置，得到 $\ell(I)=a\prod_{i\in I}t_i$，$a=\ell(\varnothing)$。结果零同理为 $1-\ell(I)=(1-a)\prod_{i\in I}s_i$。单位置满足 $at_i+(1-a)s_i=1$。若 $i,j$ 可共同出现，则 $at_it_j+(1-a)s_is_j=1$。消去 $s_i,s_j$ 得 $(t_i-1)(t_j-1)=0$。所有非平凡位置必须两两排斥，构成团。反过来，团中最多出现一个位置，两结果似然均可写成常数乘单位置因子，所以后验保持乘积族。证毕。

FIB 路径图的最大排斥团只有一对相邻位置。故二结果原子读口最多直接依赖一对相邻排斥位置，三位置时就是 $\{1,2\}$ 或 $\{2,3\}$。三结果不受相同二结果结论限制，因三个不同因子化结果可以协同归一化。

## 8. 递归保持同一标签下的参数更新

### theorem 8: 因子化结果的活动权逐点更新

**Claim status: open.** 若 $\ell_o(I)=c_o\prod_{i\in I}t_{o,i}$，对应后验活动权为 $w_i'=w_it_{o,i}$。

证明。$P_w(I)\ell_o(I)\propto\prod_{i\in I}(w_it_{o,i})$，归一化即得。证毕。

二结果团读口在团外的 $t_{o,i}=1$，只需更新局部团参数。适应策略若每步由保留记录决定，并完整记录动作与返回结果，则

$$
\log w_i^{(n)}=\log w_i^{(0)}+\sum_{t=1}^n\log t_{o_t,i}.
$$

小参数更新只对已经验证的乘积活动权来源成立。任意五模式律仍需要 $\kappa$，不能用三参数族替代一般四参数概率域。全来源函数闭包判据仍为 $K_o^{\mathsf T}\mathcal V\subseteq\mathcal V$。有限个参数不等于有限精度和有限成本；值可能随历史持续变化，精确保存仍需实际实现。

## 9. 同概率量子仪器的不同后继

另行供应两个量子比特和相干操作，只研究底面四模式，不把权限视为裸 FIB 语法自带。令 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，输入 $|+\rangle|+\rangle$。

定义 $E_{\mathrm{same}}=|00\rangle\langle00|+|11\rangle\langle11|$，$P_{ij}=|ij\rangle\langle ij|$。比较

$$
\mathcal J_{\mathrm{same}}(\varrho)=E_{\mathrm{same}}\varrho E_{\mathrm{same}}
$$

与先分别读取再只报告相同的

$$
\mathcal I_{\mathrm{same}}(\varrho)=P_{00}\varrho P_{00}+P_{11}\varrho P_{11}.
$$

### theorem 9: 两种仪器有相同概率但不同共同后继关系

**Claim status: open.** 对任意输入，$\operatorname{tr}\mathcal J_{\mathrm{same}}(\varrho)=\operatorname{tr}\mathcal I_{\mathrm{same}}(\varrho)$。对 $|+\rangle|+\rangle$，结果概率均为 $1/2$，条件输出分别为

$$
|\Phi_+\rangle=(|00\rangle+|11\rangle)/\sqrt2,
\qquad \varrho_{\mathrm{mix}}=\tfrac12|00\rangle\langle00|+\tfrac12|11\rangle\langle11|.
$$

它们的经典占位概率相同，但

$$
\langle\sigma_x\otimes\sigma_x\rangle_{\Phi_+}=1,\qquad
\operatorname{tr}[\varrho_{\mathrm{mix}}(\sigma_x\otimes\sigma_x)]=0.
$$

证明。前者保留 $00$ 与 $11$ 的非对角项，后者删除它们，直接展开即得。证毕。

量子层不仅要问报告了哪个分类结果，也要问仪器是否已留下分类内部的可区分记录。丢弃环境日志不会自动恢复被记录过程改变的局部干涉。经典粗化产生关联不等于产生量子纠缠；相干输出需要相应仪器。

## 10. 关系语义与来源

一条排斥边对应三角合法事件域；两个可共同占用的端点对应四角行列式关系；二结果提供一维中心化记录空间；三结果首次容纳两项正交非零变化。金字塔把中间排斥和底面共同选择放进同一来源。记录粗化把细区别转成粗条件关联；相干后继还需分类内部非对角关系。

真正内生的边界须在实际观察与记录处理后，仍足以支持下一次更新。它不由参数最少或外形最简单自动保证。

引用的经典工具为概率图模型与条件独立（[Wainwright–Jordan 技术报告](https://statistics.berkeley.edu/tech-reports/649)），以及量子仪器的结果概率和后测量态区分（[IBM Quantum Learning](https://learning.quantum.ibm.com/course/general-formulation-of-quantum-information/general-measurements)）。这些既有理论不被声明为本卷原创。

## 11. 供应文本的实验声明

供应文本报告了 1024 张五模式二结果似然表，其中 112 张同时保持两个后验乘积结构；在 87 个有限图上检查 5982 个二结果读口；核验三结果构造的 81 份乘积后验、记录面积和协方差、12 项粗化例子及两种同概率量子仪器。原报告的脚本名为 `fib_readout_closure_checks.py`，结果名为 `fib_readout_closure_checks.json`。该报告未供应可在本次工作树读取的文件字节；这些计数是来源声明，不是本次摄入或仓库门重新验证的结果。

## 追加锚（本行以下为增补区）

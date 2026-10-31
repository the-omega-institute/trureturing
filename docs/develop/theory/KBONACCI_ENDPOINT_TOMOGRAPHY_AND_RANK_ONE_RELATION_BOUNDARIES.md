# KBonacci endpoint tomography and rank-one relation boundaries

本卷研究固定端点算子族的标量迹观察，区分任意矩阵的线性识别与严格逐元正秩一矩阵的识别。

## 1. 定位、来源与合同

**约定 1.1（读数合同）。** 固定整数 $k\ge2$，状态指标为 $0,\ldots,k-1$，并在一个域 $K$ 上工作。令

$$
r_p=(\underbrace{1,\ldots,1}_{k-p},0,\ldots,0)^{\mathsf T}
\qquad(0\le p<k),
$$

以及

$$
E_{p,t}=e_t r_p^{\mathsf T},
$$

其中 $e_t$ 是第 $t$ 个标准列向量。标量端点读数采用

$$
\Phi(A)_{p,t}=\operatorname{tr}(E_{p,t}A)=r_p^{\mathsf T}Ae_t.
$$

这是一项明确的线性观测合同。若改用 $\operatorname{tr}(E_{p,t}^{\mathsf T}A)$，以下核的行列方向全部转置。

**约定 1.2（两类算子）。** 宽度 $m=k+1$ 的单窗口合法端点集合是

$$
\mathcal D_k=\{(p,t):0\le p,t<k,\ p+t\le k\},
$$

其算子族记为 $\mathcal E_k=\{E_{p,t}:(p,t)\in\mathcal D_k\}$。允许串接任意多个合法窗口后，已有端点组合律给出全端点族

$$
\mathcal P_k=\{E_{p,t}:0\le p,t<k\}\cup\{0\}.
$$

单窗口和串接后的观察是两个不同实验合同。

**来源说明。** 现有 `KBonacciActualEndpointOperators.actual_endpoint_operators` 给出实际窗口、端点外积、允许域、串接律、正长度闭包和精确端点计数；本卷只研究这些已给定端点在标量迹读数下的线性观察几何。现有 FIB 自校准卷中的正秩一实矩阵与剪切读数属于另一载体，本卷不把两者自动识别为同一实验。

## 2. 单窗口的精确线性观察核

**定义 2.1（单窗口观察映射）。** 定义

$$
\Phi_k:\operatorname{Mat}_k(K)\longrightarrow K^{\mathcal D_k},
\qquad
\Phi_k(A)_{p,t}=\operatorname{tr}(E_{p,t}A).
$$

其第 $(p,t)$ 个坐标是矩阵 $A$ 的第 $t$ 列前 $k-p$ 个坐标之和。

**定理 2.2（端点族的张成与维数）。** 有

$$
\dim_K\operatorname{span}(\mathcal E_k)
=|\mathcal D_k|
=\frac{k^2+3k-2}{2}.
$$

更具体地，矩阵 $B$ 属于 $\operatorname{span}(\mathcal E_k)$ 当且仅当对每一行指标 $t$，其前 $t$ 个坐标相等：

$$
B_{t,0}=B_{t,1}=\cdots=B_{t,t-1},
$$

其中 $t=0,1$ 时条件为空。于是

$$
\operatorname{codim}\operatorname{span}(\mathcal E_k)
=\frac{(k-1)(k-2)}2.
$$

**证明。** 固定行 $t$。允许的 $p$ 是 $0\le p\le\min(k-1,k-t)$。当 $t=0,1$ 时，全部 $r_0,\ldots,r_{k-1}$ 构成一个三角基。当 $t\ge2$ 时，向量 $r_0,\ldots,r_{k-t}$ 的线性张成恰好由“前 $t$ 个坐标相等”的向量组成：必要性来自每个前缀向量的形状；充分性由相邻前缀之差得到坐标向量 $e_t,\ldots,e_{k-1}$，再由 $r_{k-t}$ 得到前 $t$ 个坐标的共同值。不同的行位于互不相交的矩阵坐标块，所以维数是各行维数之和。

行 $t=0,1$ 各有 $k$ 个自由度；行 $t\ge2$ 有 $k-t+1$ 个自由度。因此

$$
2k+\sum_{t=2}^{k-1}(k-t+1)
=2k+\sum_{j=2}^{k-1}j
=\frac{k^2+3k-2}{2}.
$$

允许端点对的数目同样为

$$
 k+k+\sum_{t=2}^{k-1}(k-t+1),
$$

故端点算子线性无关。∎

**定理 2.3（单窗口的不可见关系核）。** 在约定 1.1 的迹合同下，

$$
\ker\Phi_k
=\left\{X:
\begin{array}{ll}
X_{s,t}=0,&s\ge t,\\
\displaystyle\sum_{s=0}^{t-1}X_{s,t}=0,&t\ge1
\end{array}\right\}.
$$

等价地，第 $t=0,1$ 列全部为零；对 $t\ge2$，第 $t$ 列只允许出现在严格上三角位置，并且该列的前缀和为零。其维数为

$$
\dim_K\ker\Phi_k=\frac{(k-1)(k-2)}2.
$$

**证明。** 由

$$
\operatorname{tr}(E_{p,t}X)=r_p^{\mathsf T}Xe_t
=\sum_{s=0}^{k-p-1}X_{s,t},
$$

观察坐标是第 $t$ 列长度至少为 $\max(1,t)$ 的前缀和。对 $t=0,1$，所有非空前缀长度都可用，逐次相减得到整列为零。对 $t\ge2$，可用前缀长度 $k,k-1,\ldots,t$，所以得到 $X_{s,t}=0$（$s\ge t$）以及前 $t$ 项总和为零；反过来这些条件使所有可用前缀和都为零。每个 $t\ge2$ 的列贡献 $t-1$ 个自由度，求和得维数公式。秩–零化度公式继而给出 $\operatorname{rank}\Phi_k=|\mathcal D_k|$，故 $\Phi_k$ 满射。∎

**推论 2.4（小阶边界与反例）。** 当 $k=2$ 时，$\mathcal E_k$ 张成全部 $2\times2$ 矩阵，核为零。当 $k=3$ 时，核为一维，由

$$
(e_0-e_1)e_2^{\mathsf T}
$$

生成；因此两个任意矩阵 $A$ 与 $A+\lambda(e_0-e_1)e_2^{\mathsf T}$ 具有完全相同的单窗口端点读数。一般 $k\ge3$ 时，矩阵

$$
(e_0-e_1)e_2^{\mathsf T}
$$

仍是一个非零不可见方向。

**证明。** 代入定理 2.3。∎

**命题 2.5（算子作用核与标量读数核不同）。** 对任意固定端点，

$$
\ker(E_{p,t}\,\cdot)=\{x:r_p^{\mathsf T}x=0\}.
$$

但所有端点作用的共同核为零：

$$
\bigcap_{0\le p,t<k}\ker(E_{p,t}\,\cdot)=\{0\},
$$

因为 $r_0,\ldots,r_{k-1}$ 是一个三角基。故“每个操作都有非平凡核”不意味着“整个操作族对向量不可观测”；定理 2.3 的核专指把矩阵压成标量迹读数后的关系核。

## 3. 串接解除线性核

**定理 3.1（正长度端点族的满张成）。** 串接合法窗口后得到的非零端点族包含每个 $E_{p,t}$，$0\le p,t<k$。因此

$$
\operatorname{span}(\mathcal P_k)=\operatorname{Mat}_k(K),
\qquad
\bigcap_{A\in\mathcal P_k}\ker\bigl(R\mapsto\operatorname{tr}(AR)\bigr)=\{0\}.
$$

**证明。** 取端点 $(p,0)$ 的合法窗口，再取端点 $(0,t)$ 的合法窗口。端点组合律给出 $E_{0,t}E_{p,0}=E_{p,t}$，其实际词长为 $2(k+1)>0$。所有矩阵单位都可由前缀差分

$$
E_{p,t}-E_{p-1,t}=-e_t e_{k-p}^{\mathsf T}
$$

（$1\le p<k$）及 $E_{k-1,t}=e_t e_0^{\mathsf T}$ 生成。满张成后，迹配对的非退化性给出标量观察族的共同核为零。∎

**推论 3.2（继续观察与改变窗口的区别）。** 当 $k\ge3$ 时，单窗口 $m=k+1$ 的有限读数保留非零残差核；以串接词实现并逐项取得全端点族的迹读数时，全部线性关系方向都可分开。$k=2$ 时单窗口核已经为零。增加信息来自扩充可观测的测试算子族，不能由单窗口读数的后处理产生。全族满张成不保证同一条不可重置历史能够取得全族坐标。

## 4. 秩一关系的非线性识别

**定义 4.1（严格正秩一关系）。** 令

$$
\mathscr R_k^+=\{c\ell^{\mathsf T}:c,\ell\in(0,\infty)^k\}.
$$

此节取 $K=\mathbb R$。这个集合恰为严格逐元正的秩一实矩阵：反向包含可取 $c=Ae_0$、$\ell_t=A_{0,t}/A_{0,0}$，秩一使每列等于 $c\ell_t$。这里不要求对称，因而包含非对称矩阵，也包含对称的严格逐元正秩一子类；逐元正不等同于半正定。

**定理 4.2（单窗口已经分开严格正秩一类）。** 限制到 $\mathscr R_k^+$ 时，$\Phi_k$ 是单射：

$$
\Phi_k(c\ell^{\mathsf T})=\Phi_k(c'\ell'^{\mathsf T})
\quad\Longrightarrow\quad
c\ell^{\mathsf T}=c'\ell'^{\mathsf T}.
$$

**证明。** 因为 $t=0$ 时所有 $p<k$ 都合法，读数给出第一列的全部前缀和，因而给出

$$
 c\ell_0=c'\ell'_0.
$$

严格正性使 $a:=\ell_0/\ell'_0>0$，所以 $c'=ac$。对每个 $t$，端点 $(0,t)$ 合法，读数给出第 $t$ 列总和：

$$
\ell_t\sum_s c_s
=\ell'_t\sum_s c'_s
=a\ell'_t\sum_s c_s.
$$

因为 $c$ 严格正，$\sum_s c_s>0$，故 $\ell'_t=\ell_t/a$。代回得到两个外积相等。∎

**推论 4.3（结构约束可消除线性盲区）。** 当 $k\ge3$ 时，定理 2.3 的非零线性核不意味着对每一个目标类都存在碰撞。严格正秩一条件把未知矩阵限制在非线性子流形上，第一列确定对象方向，端点总和确定量具权重；对每个 $k\ge2$，单窗口已经足以恢复关系矩阵 $R=c\ell^{\mathsf T}$，但没有恢复 $c,\ell$ 的反向缩放规范。

$$
(c,\ell)\sim(a c,a^{-1}\ell),
\qquad a>0.
$$

## 5. 自校准解释与 FIB 接缝

**命题 5.1（两层校准）。** 在这个抽象合同中，自校准有两个严格不同的层次：

1. 若目标是任意关系矩阵，$k\ge3$ 时单窗口端点读数不单射，串接端点全族提供一种消除线性核的扩充；$k=2$ 时单窗口已经单射；
2. 若目标已经声明为严格正秩一关系，单窗口读数对每个 $k\ge2$ 都在该非线性目标类上单射，即使 $k\ge3$ 时环境线性核非零。

因此“边界状态够不够”必须相对于目标类与允许操作同时判定，不能从线性维数直接推出目标不可识别，也不能从秩一识别推出对象与量具各自绝对唯一。

**开放边界 5.2（从 KBonacci 到 FIB 的类型桥）。** 现有 KBonacci 端点算子是 $\operatorname{Mat}_k(K)$ 中的布尔支持外积，现有 FIB 自校准来源则是带正性、秩一和迹归一条件的实 $2\times2$ 矩阵，且操作族还包含 Fibonacci 推进与标签交换。要把本卷的抽象观察合同变成 FIB 的物理或来源级协议，至少需要一个显式的载体映射，证明它保持来源合法性、操作词、读数和目标等价关系。共享“端点”“秩一”等名称不足以构成桥；本卷不宣称该桥已经成立。

**命题 5.3（同名算子不是同一操作）。** 当 $k=2$ 时，KBonacci 单窗口端点包括

$$
\begin{pmatrix}1&1\\0&0\end{pmatrix},
\begin{pmatrix}1&0\\0&0\end{pmatrix},
\begin{pmatrix}0&0\\1&1\end{pmatrix},
\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

**证明。** 依次代入 $E_{0,0},E_{1,0},E_{0,1},E_{1,1}$ 即得所列矩阵。它们秩为一且有零行或零列，与严格逐元正关系矩阵的支撑不同；FIB 的可逆推进剪切则秩为二。载体和操作语义的对应仍须证明，因此不能把本卷的端点读数直接说成 FIB 的四次关系读数。∎

## 6. 来源与适用边界

**来源表态。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| `D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators.actual_endpoint_operators` | `repo-derived` 供应实际窗口、端点外积、串接律、全端点闭包、计数与非零秩至多一；不供应本卷的迹观察张成/核分类。 |
| `KBONACCI_SELF_CALIBRATING_BOUNDARIES.md` 第 3–4 节 | `repo-derived` 供应边界状态、端点命题、单窗口非闭合与 Hankel 秩；不把这些结果解释成关系矩阵的标量迹核。 |
| `FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_SYNTHESIS.md` | `repo-derived` 供应关系读数、目标相对框架与开放的类型边界；不供应 KBonacci 载体映射。 |
| 有限维线性代数与非退化迹配对 | `literature-attested` 的标准数学工具；本卷的具体端点计算是其在上述合同中的推导。 |
| 本卷的定理 2.2–4.2 | `repo-derived` 的综合推导；从上述端点合同计算张成、标量观察核与严格逐元正秩一识别，不主张文献新颖性或优先权。 |

**适用边界。** 严格逐元正秩一类允许非对称，也包含其对称子类；结论不覆盖一般半正定矩阵。迹合同固定为 $\operatorname{tr}(EA)$；改变配对、允许窗口、来源域或输出合同都需要重新计算。KBonacci 到 FIB 的载体、操作、读数与目标等价关系的类型桥保持开放。

## 追加锚（本行以下为增补区）

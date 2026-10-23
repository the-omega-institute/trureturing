# FIB-ATOM：观察者内生的三轴几何与预测接口

**约定 0.1（局部关系任务）。** 本卷的环境是相对于一个已声明操作菜单的响应对象。位移或响应差异、联合状态、原生有序树、计数、守卫和实际记录分别指定；局部方向的三维性不把这些对象合并。所有内积均为实正定内积，除非明确写为商空间之前的半正定形式；维数、正交性和误差均针对所指定的载体与度量。

**约定 0.2（中间输入及其归属）。** [观察者完成反射与可观测 Gram 演算][OBS] §§3、4、8、12 及第一处 §206“受控观察的最小行为实现”供应行为有效像、全词完成与最小稳定商；该处引用固定于 `471a0b97f30fb49acf0fcc768bb51a47944d42ba`。[稳定关系边界与三维闭合][STABLE] §§3–8 供应完整旋转合同与有符号校准的区别、单对面积与全部面积和的区别，以及忠实四元数操作输入。[递归全息边界几何][FIB] §7.2 供应纯叉积的全树替换相容性、真正三阶旋转及计数—方向联合任务的五维下界。[二阶关系完成][SECOND] §§66、110 供应局部 Bloch 接口和同一环境的 CNOT 返回。经典距离构造由 [Dokmanić 等人的距离几何注][DIST] 供应；向量积及七维边界由 [Darpö/Baez 注][VP] 供应。下列完整计算把这些结果作为 §10 同源接口桥的中间输入，不将距离重建、勾股分解、向量积分类、原生三周期或 Bloch 表示重新列为发现。

## 一、没有外部坐标时，先按可取得的关系定义环境

**定义 1.1（相容来源与实际操作菜单）。** 令 $X$ 是包含当前记录、量具标定和控制条件的来源状态集合。固定操作字母表 $\mathscr A$，每个允许生成元 $a$ 给出 $T_a:X\to X$，读出为 $o:X\to Y$。若操作有守卫，须将守卫状态及可区分失败结果包含在 $X,Y$ 中，而非在比较时删去失败词。有限词 $w=(a_1,\ldots,a_n)$ 按时间从左至右执行，约定

$$
T_w=T_{a_n}\cdots T_{a_1},\qquad T_{\varepsilon}=I,
\qquad \mathcal E_{\mathcal O}(x)(w)=o(T_wx).
$$

定义 $x\sim_{\mathcal O}y$ 当且仅当对所有 $w\in\mathscr A^*$，两者的读出相等。行为环境是 $X/{\sim_{\mathcal O}}$，行为表示的值域取有效像 $\mathcal E_{\mathcal O}(X)$，不取任意可写输出函数的集合。随机实验时，行为值改为该实际协议的完整输出分布，控制与条件事件仍属于同一实现。

所用行为商计算来自 [OBS] §§3、4、8 及上述 §206。为明确本卷的来源范围，其因子化计算如下：若两来源行为相同，则对任何后续词 $w$，

$$
\mathcal E_{\mathcal O}(T_ax)(w)
=\mathcal E_{\mathcal O}(x)(aw)
=\mathcal E_{\mathcal O}(y)(aw)
=\mathcal E_{\mathcal O}(T_ay)(w).
$$

所以操作在商上良定义，空词保持当前读出。若一个摘要 $\eta$ 使全部响应因子化，则 $\eta(x)=\eta(y)$ 蕴含 $x\sim_{\mathcal O}y$，因而 $\eta(X)\to X/{\sim_{\mathcal O}}$、$\eta(x)\mapsto[x]$ 是良定义满射。这是任务最小性，未声称恢复来源全部内部结构。

**定义 1.2（全词语义与已取得记录）。** 实际记录是一条已执行有限历史的动作、结果与控制前缀。全词行为用于判定模型能否保持任意允许接续；它不声明全部词已经执行，也不提供回到同一初态、复制未知输入、重置量具或并行取得不同协议结果的权限。以下线性模型只处理可共同标定的局部关系块。其他来源属性若属于任务，须另保留相应记录和守卫。

## 二、先有三角关系，再从共同数据建立空间

**定义 2.1（锚定距离数据与经典商构造）。** 给定同一来源、同一长度标定下的有限事件 $O,x_1,\ldots,x_N$，读数 $d(x_i,x_j)=d(x_j,x_i)\ge0$，$d(x_i,x_i)=0$，并对 $O$ 满足相同约定。$O$ 是选定参照事件。置

$$
G_{ij}=\frac{d(O,x_i)^2+d(O,x_j)^2-d(x_i,x_j)^2}{2}.
$$

要求 $G\succeq0$。此要求是共同欧氏模型的相容条件，没有先指定秩为三。所用经典锚定 Gram 构造是 Dokmanić、Parhizkar、Ranieri、Vetterli，§II.B 式 (10)，见 [DIST]；该文的 $D$ 是平方距离矩阵。其在本桥中的完整商空间计算如下。

在 $\mathbb R^N$ 上设 $g_G(s,t)=s^{\mathsf T}Gt$。若 $s^{\mathsf T}Gs=0$，对任意 $t$ 和实数 $\lambda$，半正定性给

$$
0\le(s+\lambda t)^{\mathsf T}G(s+\lambda t)
=2\lambda s^{\mathsf T}Gt+\lambda^2t^{\mathsf T}Gt.
$$

若一次项不为零，可取足够小且反号的 $\lambda$ 使右侧负，矛盾。因此 $s^{\mathsf T}Gt=0$ 对全部 $t$ 成立，即 $Gs=0$。反向显然。这证明零长度方向恰是 $\ker G$，且与全部向量正交，故

$$
K=\mathbb R^N/\ker G,\qquad
\langle[s],[t]\rangle_K=s^{\mathsf T}Gt
$$

是良定义正定内积空间。令 $\epsilon_j$ 为形式标准基、$v_j=[\epsilon_j]$，并令 $v_O=0$，则

$$
\langle v_i,v_j\rangle_K=G_{ij},\qquad
\|v_i\|_K^2=d(O,x_i)^2,
$$

$$
\|v_i-v_j\|_K^2=G_{ii}+G_{jj}-2G_{ij}=d(x_i,x_j)^2.
$$

两边非负，开平方恢复原距离。秩—零度给 $\dim K=\operatorname{rank}G$。若其他实现为 $w_j$，置 $W(s)=\sum_js_jw_j$，则 $\|W(s)\|^2=s^{\mathsf T}Gs$，所以 $\ker W=\ker G$，张成空间维数也为 $\operatorname{rank}G$。因此此维数是锚定实现的最小维数。

相同 Gram 的两个张成实现间，$\sum s_jv_j\mapsto\sum s_jw_j$ 良定义且为满射等距映射，因为两者的核均为 $\ker G$。固定 $O$ 后的标架歧义是正交变换；未固定 $O$ 时还包括平移。仅有距离不能选择手性。

**假设 2.2（欧氏模型与适用范围）。** 上述构造只实现给定共同数据，未将有限事件的秩当作全部未来来源的秩。若要把距离推广到一整个线性来源域，须另给该域的共同二次距离律；§10 明确列出这一输入。若 $G$ 有负方向，则这份精确数据没有此欧氏实现；测量误差、来源变化或非欧氏任务分别是不同模型，不能据此断言外部世界矛盾。

**定义 2.3（非相容数据的边界计算）。** 取 $d(O,x_1)=d(O,x_2)=1$、$d(x_1,x_2)=3$，则

$$
G=\begin{pmatrix}1&-7/2\\-7/2&1\end{pmatrix},\qquad
(1,1)G(1,1)^{\mathsf T}=-5.
$$

此数据不能来自同一欧氏三角形。证明即上述负平方长度，亦与三角不等式 $3\le2$ 不相容；它说明被拒的是该共同精确模型。

## 三、三根正交轴保存了什么：平方剩余量

**定义 3.1（三轴投影与勾股余量）。** 在任意实内积空间 $V$ 中，给定三个正交单位向量 $e_1,e_2,e_3$，记 $E=\operatorname{span}\{e_1,e_2,e_3\}$，

$$
r_i(x)=\langle e_i,x\rangle,
\qquad P_3x=\sum_{i=1}^3r_i(x)e_i,
\qquad \delta_3(x)=\|x\|^2-\sum_{i=1}^3r_i(x)^2.
$$

本桥所用正交分解是经典内积计算。令 $x_\perp=x-P_3x$，则

$$
\langle e_j,x_\perp\rangle
=r_j(x)-\sum_ir_i(x)\delta_{ji}=0.
$$

展开平方且交叉项为零，得到

$$
\delta_3(x)=\|x_\perp\|^2\ge0,
\qquad \delta_3(x)=0\iff x=P_3x\iff x\in E.
$$

量具的单位长度已固定。该式比较总长度与投影保存的长度，而非凭空增加隐藏变量。要由三轴恢复一个整个关系域，须对该域全部关系证明剩余量为零。

**定义 3.2（距离读出与同基准双点）。** 在定义 2.1 的共同欧氏实现中，若真实基准端点 $a_i$ 的锚定向量为 $e_i$，则余弦式给

$$
r_i(x)=\frac{d(O,x)^2+1-d(a_i,x)^2}{2}.
$$

这里 $x$ 指同一实现中的关系向量，$d(O,x)=\|x\|$。这些距离恢复投影和 $\delta_3(x)$，尚未恢复剩余方向。例如在 $\mathbb R^4$ 中取 $O=0$、$a_i=e_i$，

$$
x_+=(1,2,3,1),\qquad x_-=(1,2,3,-1).
$$

所用双点计算为

$$
\|x_\pm\|^2=15,\qquad
\|x_\pm-e_1\|^2=14,\quad
\|x_\pm-e_2\|^2=12,\quad
\|x_\pm-e_3\|^2=10.
$$

所以到四个基准的全部距离相同，三个投影为 $(1,2,3)$，剩余量为一；但 $x_+-x_-=2e_4\ne0$。双点不是同一关系点，增加仅对这些距离的后处理不能区分它们。

**定义 3.3（块 Gram 证书）。** 三轴与新关系的共同 Gram 为

$$
G_4=\begin{pmatrix}
1&0&0&r_1\\0&1&0&r_2\\0&0&1&r_3\\
r_1&r_2&r_3&\|x\|^2
\end{pmatrix}.
$$

用最后一行减去 $r_i$ 倍第 $i$ 行，行列式不变，最后一行前三项归零、最后一项为 $\delta_3(x)$。故 $\det G_4=\delta_3(x)$。当 $\delta_3(x)>0$ 时，这四个向量独立：任一零线性组合与四个向量分别取内积，得到 Gram 核中的系数列，而非零行列式使该核为零。因此共同距离数据至少需要第四方向。$\delta_3=0$ 只证明这个 $x$ 没有外部分量，不证明未比较关系的结论。

**定义 3.4（有限精度的局部预算）。** 固定已检查关系域 $D\subset V$ 及 $\varepsilon\ge0$，若对每个 $x\in D$ 有 $0\le\delta_3(x)\le\varepsilon^2$，则本桥使用的误差界为

$$
\|x-P_3x\|\le\varepsilon,
$$

$$
0\le d(x,y)^2-\|P_3x-P_3y\|^2\le4\varepsilon^2
\qquad(x,y\in D).
$$

证明。正交分解给第一式。差 $x-y=(P_3x-P_3y)+(x_\perp-y_\perp)$ 的两项正交，所以平方距离损失恰为 $\|x_\perp-y_\perp\|^2$。三角不等式使其至多 $(\varepsilon+\varepsilon)^2$。此界可以达到：取 $x=\varepsilon e_4,y=-\varepsilon e_4$。任意正 $\varepsilon$ 都允许第四方向，故误差预算不是精确秩三的证据。

## 四、正交读口的稳定效率与维数选择是两步

**定义 4.1（三维探针反解及其经典误差计算）。** 暂设关系载体 $V$ 已为三维。正交单位基 $e_i$ 的实际返回值为 $\widehat r_i=r_i+\epsilon_i$，重建 $\widehat x=\sum_i\widehat r_ie_i$。由于 $x=\sum_ir_ie_i$，

$$
\|\widehat x-x\|^2
=\left\|\sum_i\epsilon_ie_i\right\|^2
=\epsilon_1^2+\epsilon_2^2+\epsilon_3^2.
$$

输入误差和重建误差都用欧氏范数，故精确反解的最坏放大系数为一。这个内积计算是 §10 的误差输入，不是三维选择的理由。

**定义 4.2（非正交独立单位探针）。** 取三个实单位探针 $f_1,f_2,f_3\in V$，要求线性独立。令 $F:\mathbb R^3\to V$、$F\xi=\sum_i\xi_if_i$，$H=F^*F$，读出 $r=F^*x$。$H$ 正定，实际采用精确反解 $\widehat x=FH^{-1}(r+\epsilon)$。本桥所用条件数计算如下：

$$
\widehat x-x=FH^{-1}\epsilon,
\qquad
\|\widehat x-x\|^2=\epsilon^{\mathsf T}H^{-1}\epsilon.
$$

其中 $FH^{-1}F^*=I_V$，因为 $F$ 是同型。正交对角化 $H$ 后，对单位误差取最大值得

$$
\sup_{\|\epsilon\|_2=1}\|\widehat x-x\|
=\frac1{\sqrt{\lambda_{\min}(H)}}.
$$

最小特征值方向达到上界。三个探针单位长使 $\operatorname{tr}H=3$，三个正特征值之和为三，所以 $\lambda_{\min}(H)\le1$。放大系数至少一；等于一时每个特征值至少一、总和三，故全部为一。对称矩阵由正交谱分解得到 $H=I$，即探针两两正交。反向 $H=I$ 显然达到一。

独立性、单位标定、欧氏误差范数和精确逆都在此结论中承重；相关噪声加权、近似求逆或奇异探针属于另一个问题。同一证明在任意固定维数成立，因此它解释正交为何高效，却不单独选择轴数三。

## 五、无损面积与循环相容：不先假定全部旋转

**假设 5.1（全域局部关系包）。** $K$ 是有限维实正定内积空间，至少含两个独立方向。给定全域双线性 $B:K\times K\to K$，要求三线性形式 $T(u,v,w)=\langle B(u,v),w\rangle_K$ 完全交错，并在同一长度、面积标定下满足

$$
\|B(u,v)\|_K^2
=\|u\|_K^2\|v\|_K^2-\langle u,v\rangle_K^2
\qquad(u,v\in K).
$$

再要求 Jacobi 循环式

$$
\mathcal J(u,v,w)
=B(u,B(v,w))+B(v,B(w,u))+B(w,B(u,v))=0.
$$

不预先给叉积，不假设对完整 $SO(K)$ 等变，也不把有限原子值的核对替换成全域条件。非归一化关系 $B_0=\kappa B$ 的面积平方多一个 $\kappa^2$；除以实际非零有符号 $\kappa$ 才得到此合同。符号和尺度的供应范围沿用 [STABLE] §§4–6。

用于主桥的三维选择是已知向量积结果的中间输入：Darpö Theorem 1 给维数 $0,1,3,7$，Baez node14 给三维 Lie 括号及七维非 Lie 边界，见 [VP]。以下保留这份面积—Jacobi 选择的初等证明，限定其全部条件；它不是新的向量积分类。

置 $L_u(v)=B(u,v)$。完全交错性及内积非退化给 $B(u,v)=-B(v,u)$，并且

$$
\langle L_uv,w\rangle_K=-\langle v,L_uw\rangle_K,
\qquad L_u^*=-L_u.
$$

对面积二次式在 $v,w$ 处极化，减去两个平方项再除二，得

$$
\langle L_uv,L_uw\rangle_K
=\|u\|_K^2\langle v,w\rangle_K
-\langle u,v\rangle_K\langle u,w\rangle_K.
$$

左侧为 $\langle -L_u^2v,w\rangle_K$，对全部 $w$ 成立，所以

$$
L_u^2v=\langle u,v\rangle_Ku-\|u\|_K^2v. \tag{5.1}
$$

取正交单位 $u,v$，令 $c_0=B(u,v)$。交错性给 $c_0\perp u,v$，面积律给 $\|c_0\|_K=1$，因此至少三维。假设仍有单位 $z\perp u,v,c_0$。对 (5.1) 中 $u$ 作极化，得全部 $w$ 上的式子

$$
(L_uL_v+L_vL_u)w
=\langle u,w\rangle_Kv+\langle v,w\rangle_Ku
-2\langle u,v\rangle_Kw.
$$

在该 $z$ 上右侧零。另一方面 Jacobi 与反对称性给

$$
\mathcal J(u,v,w)
=(L_uL_v-L_vL_u-L_{B(u,v)})w=0,
\qquad [L_u,L_v]=L_{B(u,v)}.
$$

相减与相加于是得到

$$
L_{c_0}z=2L_uL_vz. \tag{5.2}
$$

面积律给 $\|L_{c_0}z\|_K=1$、$\|L_vz\|_K=1$。还需检查第二次作用的真实垂直条件：

$$
\langle u,L_vz\rangle_K
=T(v,z,u)=T(u,v,z)=\langle c_0,z\rangle_K=0.
$$

三输入循环置换是偶置换。因此面积律再给 $\|L_uL_vz\|_K=1$。(5.2) 左右范数分别为一和二，矛盾。有限维性使不存在这样的第四正交方向等价于 $\dim K\le3$，故恰为三。

在任一已选正向正交单位基 $f_1,f_2,f_3$ 上，完全交错三形式由 $\kappa=T(f_1,f_2,f_3)$ 决定。交错展开给 $T=\kappa\operatorname{vol}_K$，面积律在 $f_1,f_2$ 上给 $\kappa^2=1$。所以 $B=\kappa\times_K$；选取使 $\kappa=+1$ 的定向后，$B$ 才是该定向的普通叉积。若定向已固定，则必须保留 $\kappa=\pm1$，不能只靠范数删去符号。

**定义 5.2（省去 Jacobi 的定量缺陷）。** 只保留假设 5.1 的双线性、完全交错和精确面积律，并假定维数至少四。用上述正交单位 $u,v,c_0,z$，不使用 Jacobi 的极化仍给反对易式。于是

$$
\mathcal J(u,v,z)=2L_uL_vz-L_{c_0}z,
\qquad \|\mathcal J(u,v,z)\|_K\ge2-1=1.
$$

证明中两个范数依旧分别为二和一，最后用反三角不等式。真正的外部 $z$、正定性和精确归一化均不可省去；若面积式只有误差，此常数不能直接沿用。七维虚八元数叉积满足前两个几何条件、具有非零方向关系，却不满足全域 Jacobi；其保持群为 $G_2$，不是完整 $SO(7)$。因此它不反驳带 Jacobi 的结论。

**定义 5.3（单对面积与全部面积和）。** 上式的面积律只保证每个可分解 $u\wedge v$ 的范数保存；它既不恢复输入对，也不预设线性映射 $\Lambda^2K\to K$ 对全部面积和单射。沿用 [STABLE] §4.4 的中间容量计算：维数 $d$ 时 $\dim\Lambda^2K=d(d-1)/2$，七维映射到七维的核至少十四维，四维至少二维。三维归一化叉积将 $f_i\wedge f_j$ 送到带符号单位基，才对全部面积和给线性同型。

该计算由基 $f_i\wedge f_j$、$i<j$ 的个数及秩—零度得到。即使三维，$(u,v)$ 与 $(2u,v/2)$ 给相同面积记录；平行输入全给零。故“无损面积”不能偷换成原输入对、来源树或全部记录无损。

**假设 5.4（可结合操作如何供应 Jacobi）。** 若要从实际算子操作导出假设 5.1 的 Jacobi，须给实线性单射 $\Phi:K\to\mathcal A$ 到一个实结合代数，并要求像在交换子下封闭、且归一化关系精确满足

$$
\Phi(B(u,v))=\frac12[\Phi(u),\Phi(v)].
$$

这比仅给一个非忠实标签映射强。其完整传回计算为

$$
\Phi(\mathcal J(u,v,w))
=\frac14\bigl([U,[V,W]]+[V,[W,U]]+[W,[U,V]]\bigr)=0,
$$

其中 $U=\Phi(u)$、$V=\Phi(v)$、$W=\Phi(w)$。展开第一项为 $UVW-UWV-VWU+WVU$；另两项为 $VWU-VUW-WUV+UWV$、$WUV-WVU-UVW+VUW$，三重乘积逐项抵消。单射才允许由像为零推出 $\mathcal J=0$。像的闭合和因子 $1/2$ 分别保证同类型响应及归一化；结合代数本身并不自动给面积律。

忠实实现可消费 [STABLE] §§6–7 的四元数输入：在 $B$ 正向基中，$\Phi(u)=-i(u_1X+u_2Y+u_3Z)$，Pauli 乘法给 $[\Phi(u),\Phi(v)]/2=\Phi(B(u,v))$，线性独立性使 $\Phi$ 实线性单射。结合的是矩阵乘法；纯 $B$ 配对和自由有序树都仍不结合。

## 六、从两个 FIB 原子产生第三个可继续关系

**定义 6.1（有序原子与循环表）。** 在假设 5.1 的三维 $K$ 中，取正交单位 $a,b$，定义 $c=B(b,a)$。$(a,b,c)$ 为正交单位基，相对于 $B$ 的正向基是 $(a,b,-c)$。由 (5.1)、反对称性可直接核对

$$
\begin{array}{c|ccc}
B&a&b&c\\\hline
a&0&-c&b\\
b&c&0&-a\\
c&-b&a&0
\end{array}
$$

例如 $L_b^2a=-a$ 给 $B(b,c)=-a$，反序给 $B(c,b)=a$；$c=-L_ab$ 与 $L_a^2b=-b$ 给 $B(a,c)=b$。另外各对角项为零，其他项由反对称性决定。于是原始次序关系是

$$
B(b,a)=c,\qquad B(c,b)=a,\qquad B(a,c)=b.
$$

第三轴来自两个独立关系的有向响应，不是先摆进一个三维容器。

**定义 6.2（原生树与已供应的全树读出）。** 保留自由有序树

$$
\mathcal T::=\alpha\mid\beta\mid\langle s,t\rangle,
\qquad \rho\alpha=\beta,
\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

置 $q_B\alpha=a$、$q_B\beta=b$、$q_B\langle s,t\rangle=B(q_Bs,q_Bt)$。这是 [FIB] §7.2 的纯方向读出，区别于 [STABLE] §7 的含标量四元数乘法读出。令 $Ra=b,Rb=c,Rc=a$。在基 $(a,b,c)$ 上 $R$ 是三循环置换矩阵，其列正交、行列式为一，$R^3=I$ 且 $R\ne I$，故真正三阶。上述乘法表在循环置换下不变，双线性展开给

$$
B(Ru,Rv)=RB(u,v)\qquad(u,v\in K).
$$

所消费全树结果的证明为：两叶分别满足 $q_B(\rho\alpha)=b=Ra$ 和 $q_B(\rho\beta)=B(b,a)=c=Rb$。若子树 $s,t$ 满足，则

$$
q_B(\rho\langle s,t\rangle)
=B(Rq_Bs,Rq_Bt)=Rq_B\langle s,t\rangle.
$$

结构归纳处理任意有序树，包括平行输入产生零的情形，得到 $q_B\rho=Rq_B$。

实际原生像恰为

$$
q_B(\mathcal T)=\{0,\pm a,\pm b,\pm c\}.
$$

包含关系由乘法表封闭与结构归纳给出。反向，叶实现 $a,b$，$\langle\beta,\alpha\rangle$ 实现 $c$，反序实现 $-c$，$\langle\beta,\langle\beta,\alpha\rangle\rangle$ 实现 $-a$，$\langle\langle\beta,\alpha\rangle,\alpha\rangle$ 实现 $-b$，$\langle\alpha,\alpha\rangle$ 实现零。其线性张成为 $K$，但七值像不是整个连续 $K$，全域输入、任意线性组合或连续旋转不因此成为原生操作权限。

**定义 6.3（同源的加法和次序读出）。** 对同一树，另定义 $q_+\alpha=a$、$q_+\beta=b$、$q_+\langle s,t\rangle=q_+s+q_+t$。记 $\gamma=\langle\beta,\alpha\rangle$，则 $q_+\gamma=a+b$，而 $q_B\gamma=c$。相应三向量的 Gram 分别为

$$
\operatorname{Gram}(a,b,a+b)
=\begin{pmatrix}1&0&1\\0&1&1\\1&1&2\end{pmatrix},
\qquad \operatorname{Gram}(a,b,c)=I_3.
$$

第一矩阵第三列是前两列之和，前两列独立，所以秩二、行列式零；第二矩阵秩三。源相同不意味着读出相同。第二种的第三方向来自真实有序二元响应，不由重复写替换符号产生。

组成 $n(t)=(n_\alpha(t),n_\beta(t))^{\mathsf T}$ 是独立读数，满足 $n\rho=Mn$、$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$。例如 $q_B(\rho^3\alpha)=a=q_B\alpha$，但

$$
\rho^3\alpha=\langle\langle\beta,\alpha\rangle,\beta\rangle
\ne\alpha,
\qquad n(\rho^3\alpha)=(1,2)^{\mathsf T}\ne(1,0)^{\mathsf T}.
$$

这就是读出三周期与来源不三周期的直接区别。计数与方向联合线性任务的最小维数五由 [FIB] §7.2 供应，不能将两项独立任务叠放为三个线性坐标。

**定义 6.4（五模式守卫仍是来源合同）。** 沿用 [STABLE] §7.3 的原生高到低窗口：印刷三位从低到高写，窗口输入从高到低行进，组成更新为 $n'=M^3n+d_\sigma$。

| 模式 | 印刷三位 | $d_\sigma$ | 允许旧接缝 | 新接缝 |
| --- | --- | --- | --- | --- |
| $[null]$ | $000$ | $(0,0)$ | $0,1$ | $0$ |
| $[2]$ | $100$ | $(1,0)$ | $0,1$ | $1$ |
| $[3]$ | $010$ | $(0,1)$ | $0,1$ | $0$ |
| $[25]$ | $101$ | $(2,1)$ | $0$ | $1$ |
| $[5]$ | $001$ | $(1,1)$ | $0$ | $0$ |

例如 $[2][5]$ 从空接缝出发第二步失败，因为第一次输出接缝一，而 $[5]$ 只允许旧接缝零。即便某方向读出相同，该合法性差别也不能删除。$[null]$ 仍执行 $M^3$ 的来源更新，不自动成为恒等。来源位置、原树、记录和取得侧输入的费用若属于任务，须独立保留；三维局部关系不将五模式或完整树无损改成三个标签。

## 七、手性固定符号，不供应未知的第三响应

**定义 7.1（内部定向与未读分量）。** 继续使用 $c=B(b,a)$ 及三维正交单位基 $a,b,c$。对 $x\in K$，记 $r=\langle a,x\rangle_K$、$s=\langle b,x\rangle_K$、$h_x=\langle c,x\rangle_K$。经典勾股计算给

$$
|h_x|=\sqrt{\|x\|_K^2-r^2-s^2}.
$$

这里已经用到 $K=\operatorname{span}\{a,b,c\}$；若还有第四方向，右侧包含全部剩余方向的长度，并不单独等于第三投影绝对值。

在同一三维 $K$ 内，对任意实 $r,s$ 和 $h>0$，

$$
x_+=ra+sb+hc,\qquad x_-=ra+sb-hc
$$

有相同的前两投影、长度平方 $r^2+s^2+h^2$，但第三投影为 $\pm h$。证明即正交展开；两点差为 $2hc$ 非零。内部次序规定了哪一侧称为正侧，实际第三读数才区分这对来源。定义轴的规则不等于已经取得未知目标沿该轴的响应。

**定义 7.2（标架与取得合同）。** 基准端点 $c$ 若实际可作为量具端点，则第 3.2 条的距离式可读出 $h_x$；或者由另一个已供应探针直接返回 $\langle c,x\rangle_K$。仅有 $B(b,a)=c$ 的代数定义不提供这两种仪器。给定手性也不保证未知输入可以复制，或三种实验可以在一次破坏性历史中同时取得。所需取得权限是行为菜单的一部分。

## 八、三轴决定全部后续：联合来源的稳定商

**定义 8.1（联合线性来源与未来探针）。** 固定有限维实内积空间 $J$ 作为声明的联合状态域，生成元为实际线性 $U_a:J\to J$，当前读出

$$
C x=(\langle p_1,x\rangle_J,\langle p_2,x\rangle_J,
\langle p_3,x\rangle_J)^{\mathsf T},
\qquad E_0=\operatorname{span}\{p_1,p_2,p_3\}.
$$

本节先允许独立但非正交的 $p_i$。几何向量 $e_i\in K$ 与联合探针 $p_i\in J$ 是不同类型；§10 才构造它们的兼容识别。设

$$
E_{m+1}=E_m+\operatorname{span}_{a\in\mathscr A}U_a^*E_m,
\qquad E_\infty=\bigcup_{m\ge0}E_m.
$$

这里“和”是有限线性组合的空间和，菜单可无限。词的约定与第 1.1 条相同，$U_w=U_{a_n}\cdots U_{a_1}$。从 $E_0$ 开始归纳可得

$$
E_m=\operatorname{span}\{U_w^*p_i:|w|\le m,\ i=1,2,3\}.
$$

归纳步中 $U_a^*U_w^*=(U_wU_a)^*=U_{aw}^*$，对应先执行 $a$ 再执行 $w$，覆盖所有新增长度的词。递增链在有限维 $J$ 中有限步稳定；一旦 $E_{m+1}=E_m$，生成元伴随已保持该空间，后续不再增长。

以下线性完成计算消费 [OBS] §12 的正交对偶和 §8 的全生成元语义：

$$
N_\infty=\bigcap_w\ker(CU_w)=E_\infty^\perp,
\qquad Q_{\rm pred}=J/N_\infty.
$$

证明。$z\in\ker(CU_w)$ 当且仅当对全部 $i$，$\langle p_i,U_wz\rangle_J=\langle U_w^*p_i,z\rangle_J=0$；对全部词取交即得。$N_\infty$ 被每个 $U_a$ 保持，因为 $CU_wU_az=CU_{aw}z=0$。因此商承载诱导更新与当前读出；两个联合态的全部未来相等当且仅当其差在 $N_\infty$。任一保全部未来的线性摘要 $L$ 都有 $\ker L\subseteq N_\infty$，所以其像满射到此商，维数不小于 $\dim E_\infty$。这只是最小线性预测商，不是完整联合态恢复。

**假设 8.2（全向量域的当前充分判据）。** 这里当前三读数决定全部未来的范围是全部 $x,y\in J$。所用已有稳定完成判据具体化为

$$
Cx=Cy\Longrightarrow CU_wx=CU_wy\quad\forall w
\quad\Longleftrightarrow\quad U_a^*E_0\subseteq E_0\quad\forall a.
$$

正向充分性证明：若生成元伴随保持 $E_0$，有限词的伴随按正确次序复合也保持它。故 $Cx=Cy$，即 $x-y\perp E_0$，使每个 $U_w^*p_i$ 与该差正交，全部未来相等。此时 $E_\infty=E_0$，$N_\infty=\ker C=E_0^\perp$。

必要性证明：若某 $U_a^*e\notin E_0$，$e\in E_0$，取 $z=P_{E_0^\perp}U_a^*e\ne0$。当前态 $0,z$ 的读数相同，而

$$
\langle e,U_az\rangle_J
=\langle U_a^*e,z\rangle_J=\|z\|_J^2>0.
$$

$e$ 是三个探针的线性组合，故该非零值使至少一个实际读口下一步不同。这里 $0,z$ 真正在全向量域中；不能把该见证未经检查移入受限来源集。

**定义 8.3（受限实际来源的纤维判据）。** 若实际允许态为 $D\subset J$，且所有生成元保持 $D$，当前充分的精确条件是

$$
\forall x,y\in D,\quad Cx=Cy
\Longrightarrow CU_wx=CU_wy\quad\forall w.
$$

全域伴随不变仍充分，却未必必要：若 $D$ 只有一个固定零态，该条件总成立，尽管某生成元可把一个域外第四方向送到第一方向。受限行为商的像为 $D/{\sim}$，不是自动整个 $J/E_\infty^\perp$，更不自动是连续三维流形。

**定义 8.4（隐藏方向返回的共同来源双点）。** 在 $J=\mathbb R^4$ 中当前只读前三坐标。取正交更新

$$
Ue_4=e_1,\quad Ue_1=-e_4,\quad Ue_2=e_2,\quad Ue_3=e_3.
$$

同一模型的两态 $x=0,y=e_4$ 当前均给 $(0,0,0)$，下一步分别给 $(0,0,0)$、$(1,0,0)$。若改用第 3.2 条双点，则下一第一投影分别为 $1,-1$，差为二；两态原先到同一四基准的距离相同。$U^*e_1=e_4\notin E_0$，所以旧纤维被实际下一读口切开。这是三轴当前不足预测的见证，不需要在所有未来中搜索。

**假设 8.5（生成模型覆盖菜单）。** 若每个已声明生成元都有实际同源实现，且真实菜单确由它们生成，则伴随不变的归纳覆盖任意有限长度。归纳不赠送自由复位、同初态副本、反事实遍历或同时测量；它只是模型语义。缺少某个真实生成元时，结论只适用于较小菜单。

## 九、量子三轴接入局部关系，不替代位置、历史或环境

**定义 9.1（已有局部 Bloch 输入及其范围）。** 消费 [SECOND] §66 的受保护二级接口，固定 Pauli

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad \varrho_r=\frac12(I+r_xX+r_yY+r_zZ).
$$

所用局部计算如下。直接矩阵乘法给 $\sigma_i^2=I$、$XY=iZ=-YX$ 及循环式，$\operatorname{tr}(\sigma_i\sigma_j)=2\delta_{ij}$。故 $(r\cdot\sigma)^2=|r|^2I$，迹为零，使 $\varrho_r$ 特征值为 $(1\pm|r|)/2$。正性等价于 $|r|\le1$；无迹 Hermitian 关系块为三维实空间，密度态只是其中的仿射球体。

归一化 Hilbert–Schmidt 内积 $\langle A,B\rangle=(1/2)\operatorname{Re}\operatorname{tr}(A^\dagger B)$ 在该块使 $X,Y,Z$ 正交单位；对密度态差有

$$
\|\varrho_r-\varrho_s\|_{\rm HS,norm}^2=\frac14|r-s|^2.
$$

这是算符关系几何，不是位置空间。$\operatorname{tr}(XY)=0$ 与 $XY=-YX$ 同时成立，说明正交不推出对易。每个 Pauli 方差为 $1-r_i^2$，总和为 $3-|r|^2\ge2$，所以同一态的三个 Pauli 不可能同时零方差。正交关系不提供在一份未知输入上同时无损取得三个参数的仪器。取得完整参数还需实际状态制备、测量菜单与重复权限。

**定义 9.2（正交而零次序响应的两量子位输入）。** 在两量子位的反 Hermitian 实空间，取

$$
A=-iX\otimes I,\qquad D=-iI\otimes X,
\qquad \langle A,D\rangle=\frac14\operatorname{Re}\operatorname{tr}(A^\dagger D).
$$

同一内积用于所有输入。由于 $A^\dagger A=D^\dagger D=I_4$，两者范数为一；$\operatorname{tr}(X\otimes X)=\operatorname{tr}X\operatorname{tr}X=0$，所以正交。两张量因子作用于不同量子位，$AD=DA=-X\otimes X$，故 $[A,D]/2=0$，但 Gram 面积平方为一。这个计算展示结合算子与 Jacobi 不自动供应假设 5.1 的面积律。一般量子系统不因此被压成同一个三维关系载体。

**定义 9.3（已有共同环境返回输入）。** 消费 [SECOND] §110.4：系统 $S$、环境 $E$ 均为量子位，初态 $\varrho\otimes|0\rangle\langle0|$，$W$ 是以 $S$ 控制、$E$ 为目标的 CNOT。其计算为

$$
W|j,0\rangle=|j,j\rangle,
\qquad W(\varrho\otimes|0\rangle\langle0|)W^\dagger
=\sum_{j,k}\varrho_{jk}|j,j\rangle\langle k,k|.
$$

取环境迹消去 $j\ne k$，局部态成为 $\mathcal D_Z(\varrho)=(\varrho+Z\varrho Z)/2$。同一个 $W^2=I$，第二次作用于保留的同一环境，联合态与系统态都返回原值。若换成每次独立新准备环境，则是 $\mathcal D_Z^2=\mathcal D_Z$。例如 $\varrho=|+\rangle\langle+|$，共同环境第二步给 $|+\rangle\langle+|$，新环境第二步给 $I/2$。

还可在同一实际菜单中给当前纤维对：从 $|+\rangle$ 与 $|-\rangle$ 各作用一次同样 CNOT，得到联合纯态 $(|00\rangle\pm|11\rangle)/\sqrt2$。它们当前局部态均为 $I/2$，再次作用同一 $W$ 后局部分别为 $|+\rangle$、$|-\rangle$，允许 $X$ 读出为 $+1,-1$。这是同源联合区别返回的量子见证。局部三参数、历史保真、各向同性和环境预测充分性分别有自己的条件；三参数格式不证其中任一额外条件。

## 十、同源距离—读出—有序操作—预测的任务保持桥

**假设 10.1（共同实现与有限标定面）。** 固定有限维实内积联合空间 $J$、共同零参照 $O$，在本条全向量模型中态域为 $J$。给定真实来源差异 $h_1,\ldots,h_N\in J$ 张成 $J$，令 $F:\mathbb R^N\to J$、$F\xi=\sum_j\xi_jh_j$。这些差异、距离、探针、控制与后续操作属于同一来源实现，不分别选择边缘模型。

距离任务另供一个对称双线性形式 $g_D$，不预先假定它是联合内积，要求该域的距离平方律为

$$
d_D(x,y)^2=g_D(x-y,x-y),\qquad d_D(x,y)\ge0.
$$

这是一项全域线性关系模型前提；有限距离样本本身不推出它。允许不同联合态在此任务中距离零，故商之前是任务伪距离。若要求 $d_D$ 对联合态本身严格分离，则下文核为零，联合态域也必须三维。

同一组 $0,h_1,\ldots,h_N$ 的锚定 $G$ 按定义 2.1 构造，要求 $G\succeq0$。由距离平方律，$G_{jk}=g_D(h_j,h_k)$。取 $K=\mathbb R^N/\ker G$、$v_j=[\epsilon_j]$，并在这个实际构造的 $K$ 上供应完整假设 5.1 的 $B$。选正交单位 $a,b$、$c=B(b,a)$，令 $e_1=a,e_2=b,e_3=c$。此处三维是第 5 节的推论。

实际线性读口为 $C_i(x)=\langle p_i,x\rangle_J$，其中 $p_1,p_2,p_3$ 在 $J$ 中正交单位。选取形式系数 $\zeta_i\in\mathbb R^N$ 使 $[\zeta_i]=e_i$。只要求有限标定等式

$$
C_i(h_j)=\zeta_i^{\mathsf T}G\epsilon_j
=\langle e_i,v_j\rangle_K
\qquad(i=1,2,3;\ j=1,\ldots,N). \tag{10.1}
$$

不是预先给 $K\simeq E_0$ 的同型。若 $e_i$ 有真实单位端点，右侧可由第 3.2 条的共同距离取得；形式线性组合的存在不授予制备该端点的权限。式 (10.1) 必须由已供应的实际标定关系承担。

对允许有序二元操作 $D:J\times J\to J$，要求每个读出 $\beta_i(x,y)=C_i(D(x,y))$ 双线性，且同一来源标定满足

$$
\beta_i(h_j,h_k)
=\langle e_i,B(v_j,v_k)\rangle_K. \tag{10.2}
$$

不要求 $D$ 的所有记录槽都双线性；例如来源计数槽可以按加法更新。若二元操作不在任务菜单中，可省去这一项，但也省去相应操作结论。所有实际线性单元生成元 $U_a:J\to J$ 满足 $U_a^*E_0\subseteq E_0$，其中 $E_0=\operatorname{span}\{p_1,p_2,p_3\}$。菜单、共同实现及全向量域均固定。

**定理 10.2（同源标定构造最小几何—预测接口）。** 在假设 10.1 下，有由标定数据唯一决定的满射线性映射 $\Pi:J\to K$，满足

$$
\Pi h_j=v_j,\qquad
C_i(x)=\langle e_i,\Pi x\rangle_K,\qquad
g_D(x,y)=\langle\Pi x,\Pi y\rangle_K,
$$

$$
\ker\Pi=\ker C=E_0^\perp=E_\infty^\perp,
\qquad \Pi D(x,y)=B(\Pi x,\Pi y).
$$

每个允许单元生成元有唯一诱导 $A_a:K\to K$ 使 $\Pi U_a=A_a\Pi$。因此同一来源的全部有限操作词读出、距离比较及有序关系组合在 $K$ 中保持；该同源任务的最小线性预测商与最小几何实现是同一个三维接口，经下列构造的等距映射连接：

$$
J/E_\infty^\perp\ \xrightarrow{\ \overline\Pi\ }\ K,
\qquad \overline\Pi([x])=\Pi x,
\qquad E_0\ \xrightarrow{\ \Pi|_{E_0}\ }\ K.
$$

这里联合商度量取正交代表的 $J$ 内积；它与任务度量 $g_D$ 在商上相等。若仅取实际受限来源 $S\subset J$，所得有效像为 $\Pi(S)$，其全词纤维判据按第 8.3 条；不把有限原生像称为全连续接口。

**证明。** 第 2 节的经典构造给 $K$ 及其张成向量 $v_j$；第 5 节的已知面积—Jacobi 中间输入给 $\dim K=3$ 和正交基 $e_i$。以下是将它们回接到实际同一联合来源的部分。

记 $S$ 为 $3\times N$ 标定矩阵，$S_{ij}=\langle e_i,v_j\rangle_K$。基的完整性给

$$
G_{jk}=\langle v_j,v_k\rangle_K
=\sum_iS_{ij}S_{ik},\qquad G=S^{\mathsf T}S,
\qquad CF=S. \tag{10.3}
$$

若 $F\xi=0$，则 $S\xi=CF\xi=0$，所以 $\xi^{\mathsf T}G\xi=0$，第 2 节的核计算给 $\xi\in\ker G$。因此

$$
\Pi(F\xi)=[\xi] \tag{10.4}
$$

与 $F\xi$ 的系数选择无关。$F$ 满射，(10.4) 定义整个 $J$ 上的线性映射；形式商也由这些类张成，故 $\Pi$ 满射。其在 $h_j$ 上的值固定，张成性给唯一性。

对 $x=F\xi$，(10.3) 给 $C_i(x)=(S\xi)_i=\langle e_i,[\xi]\rangle_K$。三个基探针分离 $K$，所以 $\Pi x=0$ 当且仅当 $Cx=0$。又对 $x=F\xi,y=F\eta$，共同距离律给

$$
g_D(x,y)=\xi^{\mathsf T}G\eta
=\langle[\xi],[\eta]\rangle_K
=\langle\Pi x,\Pi y\rangle_K. \tag{10.5}
$$

这同时证明 $g_D$ 全域半正定，零域恰为 $\ker\Pi$；没有从一个任意三维距离模型改名得到结论。

定义 $\iota:K\to J$、$\iota(\sum_it_ie_i)=\sum_it_ip_i$。正交单位标定使 $\iota$ 等距且像为 $E_0$。刚得的读口式给 $\Pi^*e_i=p_i$，并且 $C_i(p_j)=\delta_{ij}$，故 $\Pi p_j=e_j$。因此

$$
\Pi\iota=I_K,\qquad \iota\Pi=P_{E_0},\qquad
J=E_0\oplus\ker\Pi. \tag{10.6}
$$

每个商类的唯一正交代表是 $P_{E_0}x$，其范数由 $\iota$ 的等距性等于 $\|\Pi x\|_K$。(10.5) 遂使距离商、联合正交商和几何商的度量一致。如果联合探针仅独立而不正交单位，则同样能构造线性 $\Pi$，但 (10.6) 的等距结论须按探针 Gram 修正；维数相同不能替代这个检查。

对二元操作，取 $x=F\xi,y=F\eta$。双线性读出和 (10.2) 给

$$
\begin{aligned}
C_i(D(x,y))
&=\sum_{j,k}\xi_j\eta_k\beta_i(h_j,h_k)\\
&=\left\langle e_i,B\left(\sum_j\xi_jv_j,
\sum_k\eta_kv_k\right)\right\rangle_K\\
&=\langle e_i,B(\Pi x,\Pi y)\rangle_K.
\end{aligned}
$$

当前读出式和基分离性得到 $\Pi D(x,y)=B(\Pi x,\Pi y)$。所以将任一输入改为同核来源不会改变二元操作的几何响应；这证明的是任务保持，并非 $D$ 在全部记录上等于 $B$。

生成元伴随不变使 $\ker\Pi=E_0^\perp$ 被 $U_a$ 保持：若 $z\perp E_0$，对每个 $e\in E_0$ 有 $\langle e,U_az\rangle_J=\langle U_a^*e,z\rangle_J=0$。故 $A_a(\Pi x)=\Pi U_ax$ 良定义；满射给唯一性，也可明确写为

$$
A_a=\Pi U_a\iota,
\qquad A_w=A_{a_n}\cdots A_{a_1},
\qquad \Pi U_w=A_w\Pi. \tag{10.7}
$$

最后一个等式对词长归纳：空词显然；若先执行 $w$ 再执行 $a$，则 $\Pi U_aU_w=A_a\Pi U_w=A_aA_w\Pi$。与二元桥同用，任何由这些允许操作和同源输入构成的有限表达式亦可按表达式结构归纳，保持其 $\Pi$ 值。标量距离由 (10.5) 保持，当前读出由三个坐标保持。

第 8 节的完成计算给 $E_\infty=E_0$，因此行为等价恰为差在 $\ker\Pi$。$\overline\Pi$ 既单射又满射，(10.6) 给等距性。任一保全部当前及未来的线性摘要 $L$ 必有 $\ker L\subseteq\ker\Pi$，所以其像满射到三维 $K$，维数至少三；$\Pi$ 已达到。几何方面，$G$ 秩三使任何实现这些共同锚定距离的张成载体至少三维。两个最小性现由同一个明确构造的映射结合，而非分别证三维再假定相等。距离与二元响应均已因子化，所以加入这些列明比较不会再细化这个商。证毕。

**定义 10.3（共同桥的障碍而非维数证据）。** 假设 10.1 的有限校准与生成元不变分别不可省略。在 $J=\mathbb R^3$ 取标准探针，另取 $g_D(x,y)=4x_1y_1+x_2y_2+x_3y_3$。令 $L=\operatorname{diag}(2,1,1)$，$B_D(u,v)=L^{-1}(Lu\times Lv)$，则该距离几何仍三维，$B_D$ 在 $g_D$ 下满足完全交错、精确面积与 Jacobi，因为 $L$ 将它送到标准叉积。当前读数也有三维，恒等菜单闭合，但标准 $e_1$ 的距离为二、标准读数范数为一，所以不能把两个度量按同一读数等距识别。

证明。$\|Lx\|^2=g_D(x,x)$，$LB_D(u,v)=Lu\times Lv$ 直接传回所有几何条件。距离范数 $d_D(0,e_1)=2$ 与 $\|Ce_1\|_2=1$ 不等；任何使几何正交坐标等于这些读数的映射都会给该向量长度一，矛盾。失败位置正是 (10.1)。另在 $J=\mathbb R^4$ 取 $g_D$ 只读前三坐标，则当前几何商仍三维；第 8.4 条的 $U$ 未保持隐核，预测商为四维，因为新增探针 $e_4$ 与旧三探针张成全部 $J$。这一次失败在生成元闭合，不能靠补校准代替。

**定义 10.4（真正同源的 FIB 兼容实现）。** 为给主桥一个有隐藏记录而非假定同型的实现，取

$$
J=K\oplus\mathbb R^2,
\qquad j(t)=(q_B(t),n(t)),
\qquad C(u,n)=(\langle a,u\rangle_K,
\langle b,u\rangle_K,\langle c,u\rangle_K)^{\mathsf T},
$$

$$
g_D((u,n),(v,m))=\langle u,v\rangle_K,
\qquad U_\rho(u,n)=(Ru,Mn),
\qquad D((u,n),(v,m))=(B(u,v),n+m).
$$

联合内积取正交直和，$p_i=(e_i,0)$，此处实际线性菜单先取替换 $\rho$ 的全部有限词；有序嫁接另为给定二元操作。由第 6 节已供应的树规则，$j(\rho t)=U_\rho j(t)$、$j(\langle s,t\rangle)=D(j(s),j(t))$，保持同一个来源的方向和计数。$D$ 的整体不双线性，其三个方向读出却双线性，恰为假设 10.1 所需条件。

可取真实来源差异 $h_j=j(T_{j-1})$、$j=1,\ldots,5$，$T_n=\rho^n\alpha$；参照零是另给的联合线性关系基准，不冒称一棵空树。在基 $(a,b,c)$ 与两计数坐标中，这五列为

$$
F=\begin{pmatrix}
1&0&0&1&0\\0&1&0&0&1\\0&0&1&0&0\\
1&0&1&1&2\\0&1&1&2&3
\end{pmatrix}.
$$

前五同源输出的秩五由 [FIB] §7.2 供应；在此基中，将第四行减第一、第三行，将第五行减第二、第三行，左下块归零、右下块成为 $\left(\begin{smallmatrix}0&2\\2&2\end{smallmatrix}\right)$，所以行列式为 $-4$，这些 $h_j$ 张成 $J$。其任务距离只比较方向，锚定 Gram 的列坐标为

$$
S=\begin{pmatrix}1&0&0&1&0\\0&1&0&0&1\\0&0&1&0&0\end{pmatrix},
\qquad G=S^{\mathsf T}S.
$$

所以 $G\succeq0$、秩三，$v_1=v_4=a$、$v_2=v_5=b$、$v_3=c$，可取 $\zeta_i=\epsilon_i$。有限等式 (10.1)、(10.2) 逐项由 $C,F,D$ 的显示公式成立。$U_\rho$ 的块对角形式使 $U_\rho^*E_0\subseteq E_0$，共同桥 (10.4) 构造出来的映射正是

$$
\Pi(u,n)=u,
\qquad \ker\Pi=\{0\}\oplus\mathbb R^2.
$$

证明此识别不依赖先假定同型：$\Pi h_j=v_j$，而上述五列张成 $J$，所以主定理的唯一性强制为方向投影。任意 $\rho$ 后续的方向均由 $R$ 预测；有序嫁接的方向由 $B$ 预测；计数仍按 $M$ 和加法更新。三维只对列明方向、距离任务充分。若当前读出增加计数，则同源联合线性任务恢复为五维，不能沿用三维摘要。

实际树域 $j(\mathcal T)$ 不等于整个 $J$，而其方向有效像恰为七值集。全向量线性模型的三维最小商不把原生有限行为像改成连续空间；若要求保全部树身份、五模式守卫或完整历史，须另加这些任务，按第 1.1 条重新取行为商。侧树固定时嫁接的方向映射 $u\mapsto B(q_Bs,u)$ 或 $u\mapsto B(u,q_Bs)$ 是线性的，但联合计数更新有常量项；未经另给线性状态扩张，不能把它称为本条的联合线性生成元。

**定义 10.5（标架变换的精确群）。** 同源距离实现固定参照后的自由度是 $O(3)$；若连实际有符号 $B$ 与内积一并保持，保持群是 $SO(3)$。在 $B$ 正向正交基中，等距 $Q$ 满足

$$
B(Qu,Qv)=\det(Q)QB(u,v).
$$

证明。对任意 $w$，左侧与 $Qw$ 的内积是 $\operatorname{vol}_K(Qu,Qv,Qw)=\det(Q)\operatorname{vol}_K(u,v,w)$，内积非退化得式。$B$ 非零使保持式要求 $\det Q=1$，反向亦成立。若仅同时运输结构而不固定原 $B$，任何 $Q\in O(3)$ 都可以，运输后的 $B'=QB(Q^{-1}\cdot,Q^{-1}\cdot)$ 在反射时包含相应手性符号。

换正交坐标后，读数列变为 $Qr$、诱导动力学变为 $QA_aQ^{-1}$，二元读出按同一 $Q$ 运输。若保持来源与全部标定锚点的名称不动，唯一映射已经由这些锚点固定；标架自由度指不同坐标表示，不是新增物理操作权限。未固定参照时还可整体平移，但不能混用不同原点下的位移或不同校准下的长度。

**推论 10.6（观察者的内生三轴环境）。** 对假设 10.1 的同源线性局部任务，共同距离的半正定性构造几何，精确面积与 Jacobi 选择三维，有限实际标定与全生成元闭合把该几何接到当前读口和全词预测商。因此观察者的最小局部几何—预测接口恰为三维，三个正交读口无遗漏地恢复该接口中的任意关系；该结论不自动恢复全部联合状态或取得所有实验。

证明。由定理 10.2 的同一个 $\Pi$、核等式与等距商映射，局部关系 $\Pi x$ 属于 $\operatorname{span}\{a,b,c\}$，故第 3 节剩余量严格为零，第 4 节正交误差系数为一。第 8 节归纳使全部允许后续仍由该值决定。最小性由同一定理的秩三和满射因子化下界得到，而非由当前读口数量推出。有限精度时仅适用第 3.4 条已检查域的误差预算，不把它升级为本推论的精确结论。

这个局部任务允许在同一三维几何中有任意多关系点，每点三个坐标而非整个环境三个数字；来源位置、物体标签、场值、树、量具及历史记录可继续增加。所有结论都以已列出的共同校准、可执行有序响应与完整菜单闭合为条件，不断言物理世界全局三维、全局平直、存在绝对标架，或 FIB 自由语法本身只有三维。当前余量检验遗漏的局部方向，生成元闭合检验被合并的来源区别能否在未来返回；共同标定桥才使两项检验针对同一来源和同一任务。

[OBS]: https://github.com/the-omega-institute/trureturing/blob/471a0b97f30fb49acf0fcc768bb51a47944d42ba/docs/develop/theory/FORMAL_OBSERVER_COMPLETION_REFLECTION.md
[STABLE]: AURIC_FIB_STABLE_RELATION_BOUNDARY_THREE_DIMENSIONAL_CLOSURE.md
[FIB]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md
[SECOND]: AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md
[DIST]: ../../../Library/Geometry/dokmanic2015euclideandistancematrices.md
[VP]: ../../../Library/Geometry/darpo2009vectorproduct.md

## 追加锚（本行以下为增补区）

## 11. 全域鲁棒面积—Jacobi 合同

**定义 11.1（固定尺度的全域缺陷）。** 令 $K$ 是有限维实正定内积空间，$d=\dim K\ge2$，并令 $B:K\times K\to K$ 是全域双线性映射。置

$$
T(u,v,w)=\langle B(u,v),w\rangle_K,
\qquad
\mathcal J_B(u,v,w)=B(u,B(v,w))+B(v,B(w,u))+B(w,B(u,v)).
$$

本节的结构假设是 $T$ 对三个变量完全交错；因此它是精确的反对称性假设，而不是有误差的反交错测量。固定一个已校准的归一化尺度，并取 $\alpha,\beta\ge0$。全域面积预算和全域 Jacobi 预算分别是

$$
\left|\|B(u,v)\|_K^2-\bigl(\|u\|_K^2\|v\|_K^2-\langle u,v\rangle_K^2\bigr)\right|
\le \alpha\|u\|_K^2\|v\|_K^2, \tag{11.1}
$$

$$
\|\mathcal J_B(u,v,w)\|_K
\le \beta\|u\|_K\|v\|_K\|w\|_K. \tag{11.2}
$$

这两个量词都遍历全部 $u,v,w\in K$，包括零向量；预算是相对于同一个尺度的无量纲数。若 $B$ 被乘以 $\kappa$，面积缺陷的目标系数变为 $\kappa^2$，所以不能在未校准增益时把一个任意比例的积称为满足 (11.1)。

**定理 11.2（严格鲁棒阈值）。** 在定义 11.1 的条件下，若

$$
5\alpha+\beta<1, \tag{11.3}
$$

则 $d=3$。更具体地，若 $d\ge4$ 且 $0\le\alpha<1$，则存在正交单位向量 $u,v,z$ 使得

$$
\|\mathcal J_B(u,v,z)\|_K\ge 1-5\alpha. \tag{11.4}
$$

所以任何满足 (11.1) 的 $d\ge4$ 载体都必须有

$$
\beta\ge 1-5\alpha. \tag{11.5}
$$

当 $\alpha<1/5$ 时，右端是明确的正缺陷下界。阈值外不作三维结论：若 $\alpha<1$，这些假设仍只无条件给出 $d\ge3$；若 $\alpha\ge1$，由这些预算本身不能排除 $d=2$。

**证明。** 记 $L_x y=B(x,y)$，并记面积残差为

$$
D(x,y)=\|B(x,y)\|_K^2-\bigl(\|x\|_K^2\|y\|_K^2-\langle x,y\rangle_K^2\bigr).
$$

完全交错性给 $L_x^*=-L_x$，并给 $B(x,y)\perp x,y$。取正交单位 $u,v$，置 $c=B(u,v)$。由 (11.1)，

$$
1-\alpha\le\|c\|_K^2\le1+\alpha. \tag{11.6}
$$

当 $\alpha<1$ 时 $c\ne0$；若 $d\ge4$，可取正交单位 $z$ 垂直于 $u,v,c$。

先估计反对易项。对单位向量 $w$，四次有限差分的双线性展开给出

$$
\begin{aligned}
&Q(u+v,z+w)-Q(u+v,z-w)\\
&\quad-Q(u-v,z+w)+Q(u-v,z-w)\\
&=8\bigl(\langle B(u,z),B(v,w)\rangle_K
       +\langle B(u,w),B(v,z)\rangle_K\bigr),
\end{aligned} \tag{11.7}
$$

其中 $Q(x,y)=\|B(x,y)\|_K^2$。把 $Q$ 换成面积式
$A(x,y)=\|x\|^2\|y\|^2-\langle x,y\rangle^2$，同一差分为零：这是直接展开，使用 $u,v,z$ 两两正交；$w$ 不需要再与它们正交。因此 (11.7)、(11.1) 以及
$\|u+v\|^2=\|u-v\|^2=2$ 给出

$$
\left|\langle B(u,z),B(v,w)\rangle_K
+\langle B(u,w),B(v,z)\rangle_K\right|
\le\frac{\alpha}{8}
\bigl(\|u+v\|^2+\|u-v\|^2\bigr)\cdot
\bigl(\|z+w\|^2+\|z-w\|^2\bigr)
=2\alpha. \tag{11.8}
$$

而

$$
R=(L_uL_v+L_vL_u)z
$$

满足

$$
\langle R,w\rangle_K
=-\langle B(v,z),B(u,w)\rangle_K
 -\langle B(u,z),B(v,w)\rangle_K.
$$

对所有单位 $w$ 使用 (11.8)，得到

$$
\|R\|_K\le2\alpha. \tag{11.9}
$$

令 $x=L_vz$. 交错性和 $z\perp c$ 给

$$
\langle x,v\rangle=\langle x,z\rangle=0,\qquad
\langle x,u\rangle=T(v,z,u)=T(u,v,z)=\langle c,z\rangle=0. \tag{11.10}
$$

两次使用 (11.1)，并注意 $\alpha<1$，便有

$$
\|x\|^2\ge1-\alpha,\qquad
\|L_ux\|^2\ge(1-\alpha)\|x\|^2\ge(1-\alpha)^2,
$$

从而

$$
\|L_uL_vz\|\ge1-\alpha. \tag{11.11}
$$

同理，$c\perp z$，故由 (11.6) 和 (11.1)

$$
\|L_cz\|^2\le(1+\alpha)\|c\|^2\le(1+\alpha)^2,\qquad
\|L_cz\|\le1+\alpha. \tag{11.12}
$$

最后，交错性把 Jacobi 和写成

$$
\mathcal J_B(u,v,z)=L_uL_vz-L_vL_uz-L_cz
=2L_uL_vz-L_cz-R. \tag{11.13}
$$

反三角不等式、(11.9)、(11.11)、(11.12) 给出 (11.4)。若 (11.2) 成立，单位三元组又给
$\beta\ge\|\mathcal J_B(u,v,z)\|\ge1-5\alpha$，即 (11.5)。在 (11.3) 下 $\alpha<1/5<1$，故 $d\ge4$ 不可能。另一方面，(11.6) 在 $\alpha<1$ 时排除 $d=2$：非零的 $c$ 同时垂直于两个正交单位向量，必须提供第三方向。因此 $d=3$。证毕。

**推论 11.3（低维、缩放与阈值外边界）。** 在维数二，完全交错性使 $B(u,v)$ 同时垂直于 $K$ 的两个独立方向，所以 $B=0$；它的最小面积预算是 $\alpha=1$，而 Jacobi 预算为 $\beta=0$。在维数三，取任意定向正交叉积 $\times$ 和 $B_\kappa=\kappa\times$，则

$$
|D_\kappa(u,v)|=|\kappa^2-1|
 (\|u\|^2\|v\|^2-\langle u,v\rangle^2),\qquad
\mathcal J_{B_\kappa}=0. \tag{11.14}
$$

**证明。** 二维时三线性完全交错形式为零，内积非退化故 $B=0$；取正交单位对使面积项为一，得到最小 $\alpha=1$。三维标准叉积的范数恒等式和 Jacobi 恒等式分别把两项缩放为 $\kappa^2$ 倍和零，故 (11.14) 成立；正交单位对达到面积比的上确界，因而预算是最小的。$\kappa=\pm1$ 保留零面积缺陷下的两种手性。对 $\alpha<1$，定理 11.2 的无条件结论确实是至少三维；超过严格阈值时不能把三维结论冒称为已证。

**命题 11.4（七维精确供应者的分析边界）。** 令 $K=\operatorname{Im}\mathbb O$ 为正定实八元数的虚部，取
$B(u,v)=(uv-vu)/2$。为固定乘法和符号，取 $\mathbb O=\mathbb H\oplus\mathbb H$，约定

$$
(a,b)(c,d)=(ac-\bar d b,\;da+b\bar c),\qquad
\overline{(a,b)}=(\bar a,-b),\qquad
N(a,b)=|a|^2+|b|^2.
$$

四元数基满足 $ij=k$、$jk=i$、$ki=j$，反序变号，且 $i^2=j^2=k^2=-1$。取正交单位基

$$
e_1=(i,0),\ e_2=(j,0),\ e_3=(k,0),\ e_4=(0,1),
e_5=(0,i),\ e_6=(0,j),\ e_7=(0,k).
$$

由此乘法得到的有向三元组是

$$
(1,2,3),(1,4,5),(1,7,6),(2,4,6),
(2,5,7),(3,4,7),(3,6,5),
$$

使 $e_i\times e_j=e_k$ 沿有向三元组循环、反序变号，并令 $e_i\times e_i=0$；这里 $\times=B$。Darpö 的 Theorem 1 与 Baez 的 §4.1 在此只供应经典精确七维向量积的背景；本条用上述明确约定核对范数律和所需边界。在此同一正交标架中，面积预算为零，最小全域 Jacobi 预算为 $3$；对任意实数 $\kappa$，$\kappa B$ 的最小预算是 $(|\kappa^2-1|,3\kappa^2)$。直接取
$u=e_3,v=e_5,w=e_7$ 得

$$
\begin{aligned}
 e_3\times(e_5\times e_7)&=-e_1,\\
 e_5\times(e_7\times e_3)&=-e_1,\\
 e_7\times(e_3\times e_5)&=-e_1,
\end{aligned}
\qquad
\mathcal J_B(e_3,e_5,e_7)=-3e_1. \tag{11.15}
$$

**证明。** 把上述七个基代入二元组乘法，得到所列有向表；每个无序异基对恰在一个三元组中，故该表确定同一个 $B$ 的全部系数。$\langle B(e_i,e_j),e_k\rangle$ 在每个有向三元组的偶置换上为 $1$、奇置换上为 $-1$，其余为零，三线性展开给完全交错性。

范数律须对全部输入核对。四元数范数的乘法性和实部的循环不变性给

$$
\begin{aligned}
N((a,b)(c,d))
&=|ac-\bar d b|^2+|da+b\bar c|^2\\
&=|a|^2|c|^2+|d|^2|b|^2+|d|^2|a|^2+|b|^2|c|^2\\
&\quad-2\operatorname{Re}(ac\bar b d)+2\operatorname{Re}(dac\bar b)\\
&=(|a|^2+|b|^2)(|c|^2+|d|^2).
\end{aligned}
$$

最后的交叉项相消只用结合的四元数乘法与 $\operatorname{Re}(rs)=\operatorname{Re}(sr)$，未把八元数乘法当作结合。对虚八元数 $u=(a,b)$，$\bar a=-a$，同一乘法给 $u^2=-N(u)1$。极化得
$uv+vu=-2\langle u,v\rangle1$；共轭公式又给 $\overline{uv}=\bar v\bar u=vu$，故 $B(u,v)$ 为虚部，且

$$
uv=-\langle u,v\rangle1+B(u,v),\qquad
\|u\|^2\|v\|^2=N(uv)=\langle u,v\rangle^2+\|B(u,v)\|^2.
$$

这证明所列同一个积的全输入面积律，包括零输入和平行输入。作为同一符号约定的具体核对，
$B(e_1+e_2,e_4+e_7)=e_5+e_6+e_6-e_5=2e_6$，平方范数与面积平方都为 $4$。

表中 $e_5\times e_7=e_2$、$e_7\times e_3=e_4$、$e_3\times e_5=-e_6$，而
$e_3\times e_2=e_5\times e_4=-e_1$、$e_7\times e_6=e_1$，逐项给出 (11.15)。面积律使每个嵌套项的范数至多为 $\|u\|\|v\|\|w\|$，三角不等式给全域上界 $3$；(11.15) 在单位三元组上达到 $3$，所以最小全域 Jacobi 预算正是 $3$。缩放后的面积残差为
$(\kappa^2-1)(\|u\|^2\|v\|^2-\langle u,v\rangle^2)$，Jacobi 为 $\kappa^2\mathcal J_B$，得到所列最小预算；面积预算由正交单位对达到。该七维计算不把 $\Lambda^2K\to K$ 要求为同构，也不加入比向量积范数恒等式更强的 Gram 恒等式。

## 12. 完整已知标架上的有限系数误差证书

**定义 12.1（完整标架和取得条件）。** 另行供应一个已知维数 $d$ 以及完整正交单位标架
$e_1,\ldots,e_d$，即 $K=\operatorname{span}\{e_i\}$ 且
$\langle e_i,e_j\rangle=\delta_{ij}$ 是独立校准的精确事实。这里“完整”是来源合同中的已知覆盖，不是从有限样本发现未知环境维数。对每个有序 $(i,j)$，在同一来源版本、同一尺度和同一控制条件下准备 $(e_i,e_j)$，执行有序二元操作，并用第 $k$ 个标架探针取得

$$
 b_{kij}=\langle B(e_i,e_j),e_k\rangle.
$$

若一次操作会破坏来源，必须由同一来源身份的重复准备和控制完成全部 $d^3$ 个三标量；若操作可逆，则重复控制仍须证明标定没有漂移。重复准备、复位、共同初态、探针归属、动作次序和读出宽度都是实际额外假设；原生菜单没有它们时，本证书不替代这些权限。

设标量取得给出已认证的确定性区间

$$
|\widehat b_{kij}-b_{kij}|\le\epsilon_{kij},\qquad
E=\left(\sum_{k,i,j=1}^d\epsilon_{kij}^2\right)^{1/2}. \tag{12.1}
$$

若所有标量误差都由一个上界 $\epsilon$ 控制，则可直接取 $E\le d^{3/2}\epsilon$。区间须包含制备、控制、标量读数和共同校准的全部确定性误差；统计置信度若要使用，必须另给其抽样与失败合同，不能把概率保证写成 (12.1)。

由测得系数定义双线性张量

$$
\widehat B(x,y)=\sum_{k,i,j}\widehat b_{kij}x_i y_j e_k,
\qquad
M=\left(\sum_{k,i,j}\widehat b_{kij}^{\,2}\right)^{1/2}.
$$

测得的 $\widehat b_{kij}$ 不要求任何交错关系，$\widehat B$ 可不反对称；真实 $T$ 的精确完全交错性是维数选择所需的独立结构前提，不能从它推断测量噪声也交错。

把有限多项式

$$
P_A(x,y)=\|\widehat B(x,y)\|^2-
(\|x\|^2\|y\|^2-\langle x,y\rangle^2)
$$

唯一收集成
$P_A(x,y)=\sum_{|\mu|=|\nu|=2}a_{\mu\nu}x^\mu y^\nu$，并置
$R_A=\sum_{\mu,\nu}|a_{\mu\nu}|$。同样，把

$$
P_J(x,y,z)=\widehat B(x,\widehat B(y,z))
+\widehat B(y,\widehat B(z,x))
+\widehat B(z,\widehat B(x,y))
$$

的每个坐标唯一收集成
$P_{J,k}(x,y,z)=\sum_{i,j,l}q_{kijl}x_i y_j z_l$，置
$R_J=\sum_{k,i,j,l}|q_{kijl}|$。直接按上式的参数次序展开，系数为

$$
q_{kijl}=\sum_{m=1}^d\left(
\widehat b_{kim}\widehat b_{mjl}
+\widehat b_{kjm}\widehat b_{mli}
+\widehat b_{klm}\widehat b_{mij}\right).
$$

这些是分别只有
$\binom{d+1}{2}^2$ 和 $d^4$ 个有限系数的确定性和，不是紧致性给出的未知常数。

若实际算术程序输出 $M_0,R_{A,0},R_{J,0}$ 以及已认证的绝对上误差
$\eta_M,\eta_A,\eta_J$，使用

$$
\overline M=M_0+\eta_M\ge M,\qquad
\overline R_A=R_{A,0}+\eta_A\ge R_A,\qquad
\overline R_J=R_{J,0}+\eta_J\ge R_J. \tag{12.2}
$$

区间向上舍入直接给出同样的三个上界；精确有理或代数算术时相应 $\eta$ 可以为零。定义可直接验算的预算

$$
\alpha_{\rm cert}=\overline R_A+(2\overline M+E)E, \tag{12.3}
$$

$$
\beta_{\rm cert}=\overline R_J+3(2\overline M+E)E. \tag{12.4}
$$

若该有限算术结果满足 $5\alpha_{\rm cert}+\beta_{\rm cert}<1$，且完全交错性是独立的精确结构假设，则定理 11.2 认证 $\dim K=3$。

**定理 12.2（证书的正确性）。** 在定义 12.1 的完整标架和 (12.1)–(12.2) 下，真实 $B$ 满足 (11.1)–(11.2)，其中可以取
$\alpha=\alpha_{\rm cert}$、$\beta=\beta_{\rm cert}$。

**证明。** 对任意 $x,y$，Cauchy–Schwarz 直接给

$$
\|(B-\widehat B)(x,y)\|
\le E\|x\|\|y\|. \tag{12.5}
$$

故 $\|\widehat B(x,y)\|\le M\|x\|\|y\|$，而
$\|B(x,y)\|\le(M+E)\|x\|\|y\|$。对单位 $x,y$，平方范数的差满足

$$
\bigl|\|B(x,y)\|^2-\|\widehat B(x,y)\|^2\bigr|
\le(2M+E)E. \tag{12.6}
$$

每个 $P_A$ 单项在单位球上的绝对值不超过一，所以
$|P_A(x,y)|\le R_A\le\overline R_A$；(12.6) 给出 (11.1) 和 (12.3)，再按齐次性推广到任意 $x,y$。

令 $\Delta=B-\widehat B$。对 $P_J$ 定义中相同参数次序的一项，双线性给出精确分解

$$
B(x,B(y,z))-\widehat B(x,\widehat B(y,z))
=\Delta(x,B(y,z))+\widehat B(x,\Delta(y,z)).
$$

因此，不论 $\widehat B$ 是否交错，均有

$$
\begin{aligned}
&\|B(x,B(y,z))-\widehat B(x,\widehat B(y,z))\|\\
&\quad\le E\|x\|\|B(y,z)\|
 +M\|x\|\|B(y,z)-\widehat B(y,z)\|\\
&\quad\le(2M+E)E\|x\|\|y\|\|z\|.
\end{aligned} \tag{12.7}
$$

对另两项循环置换 $x,y,z$ 后相加，得到
$\|\mathcal J_B(x,y,z)-P_J(x,y,z)\|\le3(2M+E)E\|x\|\|y\|\|z\|$。
对单位 $x,y,z$，每个坐标单项的绝对值不超过一，故

$$
\|P_J(x,y,z)\|_2
\le\sum_k|P_{J,k}(x,y,z)|
\le\sum_{k,i,j,l}|q_{kijl}|=R_J\le\overline R_J.
$$

三角不等式及 $M\le\overline M$ 给 (12.4) 的预算；按三线性齐次性推广到任意输入，任一输入为零时两边均为零，得到 (11.2)。这一证明从未交换 $\widehat B$ 的两个参数，也未从真实 $T$ 的完全交错性给它增加结构先验。证毕。

**说明 12.3（零误差和七维检查）。** 对精确三维标准叉积系数，$E=\eta_M=\eta_A=\eta_J=0$，有 $R_A=R_J=0$，所以证书给出 $(\alpha_{\rm cert},\beta_{\rm cert})=(0,0)$。对命题 11.4 的明确乘法和正交标架，取精确七维系数及零算术误差，则该命题的全输入面积律使 $P_A$ 为零多项式，故唯一收集后的全部 $a_{\mu\nu}=0$，$R_A=0$。同一张量的 Jacobi 系数有 $168$ 个非零项，每项绝对值为 $3$：有序互异三元组共 $7\cdot6\cdot5=210$ 个，其中七条 Fano 线上的 $7\cdot6=42$ 个为零，其余 $168$ 个各只输出一个带符号的 $3e_k$。因此 $R_J=504$，本系数绝对值和证书给 $\beta_{\rm cert}=504$，而 (11.15) 和全域上界给出的真实最小预算是 $3$。这一有限证书允许保守上界，不把 $R_J$ 冒称为最小常数；两种预算均不通过严格三维阈值。因此本证书检验的是平方面积残差，而不是强加一个七维不成立的全 Gram 或楔平方同型条件。

## 13. 只替换代数供应者时的 §10 同源消费者

**假设 13.1（精确桥的保留面）。** 只把 §10 中“精确面积—Jacobi 代数供应者”替换为定理 11.2、12.2 的供应者，仍保留以下精确条件：共同来源和共同零参照 $O$；态域 $J$ 的有限维全向量模型；$h_1,\ldots,h_N$ 张成 $J$；同一来源上的全域二次距离律 $d_D(x,y)^2=g_D(x-y,x-y)$；$G\succeq0$ 的锚定距离数据；正交单位实际探针 $p_1,p_2,p_3$；全部 (10.1) 的有限距离—读出校准；允许二元操作的全部 (10.2) 双线性读出校准；以及每个实际线性生成元的
$U_a^*E_0\subseteq E_0$、完整菜单和同源执行条件。若要消费二元响应，$D$ 的三个方向读出仍须对同一来源双线性；计数、守卫、失败和历史槽仍按原 §10 单独保留。

在载体 $K$ 中选正交单位 $a,b$，并用有符号次序定义

$$
c=B(b,a),\qquad s=\|c\|,\qquad e_3=c/s. \tag{13.1}
$$

在 $5\alpha+\beta<1$ 下，定理 11.2 给 $\dim K=3$，而 (11.1) 给
$s^2\in[1-\alpha,1+\alpha]$，故 $s>0$，$(a,b,e_3)$ 是完整正交单位标架。这里的 $e_3$ 保留 $c$ 的实际符号和手性；不能以 $|c|$ 或未经说明的反向向量替换它。

若原标定是对 $c$ 通道的标量，替换后的精确校准式必须明确写为

$$
C_3(h_j)=\langle e_3,v_j\rangle_K
=s^{-1}\langle c,v_j\rangle_K,\qquad
\beta_3(h_j,h_k)=\langle e_3,B(v_j,v_k)\rangle_K
=s^{-1}\langle c,B(v_j,v_k)\rangle_K. \tag{13.2}
$$

也可以直接把 $e_3$ 作为独立正交探针校准；两者都要求实际的尺度 $s$ 和符号归属已经由同源合同供应。代数式 $c=B(b,a)$ 本身不授权制备端点 $c$，因此本消费者不假定能够准备归一化端点；它只要求一个实际的第三探针或一组共同距离/读出校准来承载 (13.2)。

**定理 13.2（条件消费者）。** 假设 13.1、定理 11.2 的严格阈值以及 (13.2) 的精确归一化校准成立，则 §10 的定理 10.2、其映射 $\Pi$、核等式、距离等距性、二元读出因子化和生成元预测闭合均按原证明成立，只需把原来的第三基向量替换为 (13.1) 的 $e_3$。有限系数的噪声只认证 $\alpha_{\rm cert},\beta_{\rm cert}$ 和维数选择；它不把近似系数自动提升为 (10.1)、(10.2) 的精确共同来源等式。

**证明。** 定理 11.2 供应三维性，(13.1) 供应带符号的正交单位第三方向，(13.2) 正是 (10.1)、(10.2) 的第三坐标版本。其余两坐标和所有距离、张成、探针、生成元不变及菜单条件没有改变。因此 §10 证明中的矩阵 $S$、$G=S^{\mathsf T}S$、商映射 $\Pi$、二元双线性展开和词长归纳逐字适用；唯一改变是第三行使用 $e_3$，并在原始 $c$ 读数时显式除以 $s$。证毕。

**边界 13.3（本单元未解决的取得问题）。** 近似交错、近似内积、未知或不完整方向、全套带噪的 (10.1)/(10.2) 校准、把有限标定外推到未知方向，以及无限时间的近似预测都不由定理 12.2 或定理 13.2 解决。若标架不是完整的，证书只作用于其张成子空间；若共同来源、复位／重复准备或实际第三探针不具备，相关式只能标为附加假设。已知完整标架的有限证书是模型一致性检查，不是发现未知环境维数。

## 14. 来源范围、复用和适用边界

本批的仓内推导是定理 11.2 的鲁棒反对易估计、定理 12.2 的有限系数误差传播和定理 13.2 的条件消费者。命题 11.4 复用经典七维八元数积，并在明确的乘法和正交标架中核对全输入面积律、Jacobi 缺陷及缩放边界；它不把经典向量积另算为新发现。已有卷 [STABLE] §8.2 的完整有限群 Hilbert–Schmidt 标准、[FIB] §§7–8 的原生切面与外部方向障碍、[量子测量相对边界](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) §§13–14 的固定五模逆／样本预算只作为供应者复用，不在此重写，也不把它们的有限样本升级为全域近似选择。

Darpö, *Vector product algebras*, arXiv:0810.5464v1, Theorem 1 是带相容形式的精确向量积分类；Baez, *The Octonions*, §4.1 是精确的八元数与 $G_2$ 背景。钉版 mathlib Mathlib/LinearAlgebra/CrossProduct.lean 的 cross_dot_cross 与 jacobi_cross 只供应固定 Fin 3 的精确恒等式，不能替代未知维数的全域近似选择。本地 mathlib 不作为本批前提，公开生态检索也未覆盖全部近似向量积、稳健秩识别或有限关系检验文献；这里不作全局原创性或穷尽检索声明。所有实际物理端点、重复准备、控制复位、标量精度和来源身份仍须由相应合同另行供应。

## 追加锚（本行以下为增补区）

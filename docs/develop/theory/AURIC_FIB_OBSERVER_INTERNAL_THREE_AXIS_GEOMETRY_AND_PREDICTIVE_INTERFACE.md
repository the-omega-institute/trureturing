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


## 15. 有限协方差菜单与带标签的运输场

本节把第 10 节的同一来源 $J$、同一映射 $\Pi:J\to K$ 和同一 $g_D$ 保持不变。新增的对象是一个实际许可的有限运输菜单；它不是第 10 节的二元读出，也不是把一个括号运算重新命名为第三个噪声方向。写 $B:=\Pi(S)\subseteq K$，其中 $S\subseteq J$ 是实际允许的来源域。令 $X_0,X_1,\ldots,X_m$ 是 $S$ 邻域上的光滑向量场。$X_a$ 的标签是实际合同中的控制名称，$X_0$ 是同一合同中的共同漂移。对一个常数实对称半正定矩阵 $Q$，定义

$$
\mathcal L_Q f=X_0f+\frac12\sum_{a,b=1}^mQ_{ab}X_aX_bf,
\qquad
\Gamma_Q(f,g)=\sum_{a,b=1}^mQ_{ab}(X_af)(X_bg).
\tag{15.1}
$$

这里 $\Gamma_Q$ 是该实际时钟中二阶矩率；它不是一组已经取得的有限样本。称一个有限菜单 $(Q^1,\ldots,Q^r)$ 为完整的，若每个 $Q^\ell$ 是实际允许的正定协方差，且

$$
\operatorname{span}_{\mathbb R}\{Q^1,\ldots,Q^r\}=\operatorname{Sym}_m.
\tag{15.2}
$$

对 $x\in S$ 写

$$
v_a(x):=d\Pi_xX_a(x)\in T_{\Pi(x)}K,
\qquad
T_{ab}(x):=\tfrac12(v_a\otimes v_b+v_b\otimes v_a).
\tag{15.3}
$$

**定义 15.1（来源匹配的菜单证书）。** 完整菜单满足下列条件时，称 $(S,\Pi,X_0,\ldots,X_m)$ 有一个菜单证书。先要求 $S$ 是允许带边界的光滑源域，$B$ 是光滑域，且 $\Pi|_S:S\to B$ 是满射光滑下沉；每个纤维 $F_y=S\cap\Pi^{-1}(y)$ 非空。

1. 对每个 $\ell$ 和每个 $\varphi\in C^\infty(B)$，存在 $\overline{\mathcal L}_{\ell}\varphi\in C^\infty(B)$，使 $\mathcal L_{Q^\ell}(\varphi\circ\Pi)=(\overline{\mathcal L}_{\ell}\varphi)\circ\Pi$ 在 $S$ 上成立。
2. 对每个连通的纤维 $F_y=S\cap\Pi^{-1}(y)$，实际控制合同提供一个光滑的带符号锚：在 $B$ 的每个坐标邻域内，选一个标签 $a_*$ 和一个光滑余向量 $\lambda_y$，使选定的光滑向量场 $\widehat v_{a_*}$ 满足 $\lambda_y(\widehat v_{a_*})>0$（在其非零域上）、$\widehat v_{a_*}\otimes\widehat v_{a_*}=T_{a_*a_*}$，并且其符号由一次实际的同源有符号校准固定。不同邻域的锚在重叠处相等。零点要求由这些非零域上的光滑延拓承担；若某个纤维上所有控制投影都为零，则全部场在那里定义为零。这个条件只供应方向和手性，不供应新的控制权限。
3. $S$、$B$ 和全部控制流的共同生存域已经给定；控制只能在该域的守卫内执行。若 $S$ 有边界，退出边界就是声明的死亡事件。

条件 2 是有意写出的非协方差条件。协方差只给平方和，不能给一个有标签向量的正向。条件 3 也不从投影自动得到；它是源、守卫和寿命的合同。

**引理 15.2（有限菜单恢复带标签的二阶张量）。** 若菜单证书的第 1 项成立，则每个 $T_{ab}$ 在每个连通纤维上为常数。若 $F_y$ 连通，则在给定锚之后存在唯一的光滑向量场 $\overline X_a$、$a=1,\ldots,m$，使

$$
d\Pi\,X_a=(\overline X_a\circ\Pi)\quad\text{在 }S\text{ 上}.
\tag{15.4}
$$

证明。对基本函数 $f=\varphi\circ\Pi$、$g=\psi\circ\Pi$，由 (15.1) 和第 1 项，$\Gamma_{Q^\ell}(f,g)$ 在 $F_y$ 上为常数。其值是

$$
\sum_{a,b}Q^\ell_{ab}\,d\varphi(T_{ab})d\psi.
\tag{15.5}
$$

由 (15.2) 和对称矩阵的线性独立性，所有 $T_{ab}$ 在纤维上为常数。现在用一个初等事实：若实向量组 $(u_a)$、$(w_a)$ 满足

$$
\operatorname{sym}(u_a\otimes u_b)=
\operatorname{sym}(w_a\otimes w_b)\quad\text{对所有 }a,b,
\tag{15.6}
$$

则或者两组都全为零，或者存在一个 $\epsilon\in\{+1,-1\}$ 使 $w_a=\epsilon u_a$ 对所有 $a$ 成立。事实上，选 $u_{a_*}\ne0$；对 $a=b=a_*$，秩一张量给 $w_{a_*}=\epsilon u_{a_*}$。映射 $z\mapsto\operatorname{sym}(u_{a_*}\otimes z)$ 是单射，故交叉项给 $w_b=\epsilon u_b$。若没有非零向量，结论显然。

把这个事实应用于纤维中的两个点。$T_{ab}$ 常数，所以它们之间的符号只能是一个共同的 $\epsilon$；在非零区域它随点连续，连通性使其在整个 $F_y$ 上恒定。条件 2 的带符号锚取 $\epsilon=+1$，并用 (15.6) 恢复每个其余标签。重叠锚的一致性使所得场光滑；在全为零的开集上令相应场为零，并由锚的重叠延拓。于是 (15.4) 成立且唯一。证毕。

**定理 15.3（共同漂移也下降）。** 在引理 15.2 的条件下，存在唯一的光滑向量场 $\overline X_0$ 在 $B$ 上，使

$$
d\Pi\,X_0=(\overline X_0\circ\Pi)\quad\text{在 }S\text{ 上},
\tag{15.7}
$$

并且每个菜单生成元满足

$$
\overline{\mathcal L}_{\ell}\varphi
=\overline X_0\varphi
+\frac12\sum_{a,b}Q^\ell_{ab}\overline X_a\overline X_b\varphi.
\tag{15.8}
$$

证明。由 (15.4)，对基本函数有

$$
X_aX_b(\varphi\circ\Pi)=
(\overline X_a\overline X_b\varphi)\circ\Pi.
\tag{15.9}
$$

从任意一个菜单成员中减去右端的二阶项，得到 $(X_0\varphi)\circ\Pi$。第 1 项说明这个一阶量在每个纤维上恒定；对坐标函数 $\varphi=y^i$，这些常数正是 $d\Pi X_0$ 的坐标，组成光滑向量场 $\overline X_0$。代回即得 (15.8)。若两个场满足 (15.7)，它们在每个坐标函数上的值相等，故唯一。证毕。

**推论 15.4（有限菜单的充分性与识别边界）。** 完整菜单的条件是一个有限、源匹配的充分条件：它把每个实际命名控制的投影场和共同漂移都下降到 $B$。对不完整菜单，令 $M=\operatorname{span}\{Q^1,\ldots,Q^r\}$；菜单值保证能以线性组合恢复 $\sum_{a,b}Q_{ab}T_{ab}$、$Q\in M$。在把 $T_{ab}$ 当作独立未知张量的线性反演中，$M$ 之外没有这样的普遍线性恢复式；这不排除使用 $T_{ab}=\operatorname{sym}(v_a\otimes v_b)$ 的共同因子约束作非线性识别。即使菜单完整，仅凭协方差而没有带符号锚，也只能确定

$$
\{\overline X_a\}\quad\text{模共同纤维内符号 }\overline X_a\mapsto-\overline X_a,
\tag{15.10}
$$

而不能从协方差数据选择带标签控制的共同正向。

证明。完整菜单的结论由引理 15.2 和定理 15.3 给出。线性恢复式的系数恰给 $Q$ 为菜单矩阵的线性组合；反向由同一组合直接恢复。共同因子约束则不是线性未知量的自由变化，故该线性判据不提供一般的不可识别性结论。

具体地，在 $\dim K=m$ 且实际投影帧矩阵 $V=(v_1,\ldots,v_m)$ 可逆时，任意同数据帧 $W$ 都形如 $W=VR$，其中

$$
G_{\mathcal Q}:=\{R\in\operatorname{GL}_m(\mathbb R):
RQ^\ell R^{\mathsf T}=Q^\ell\text{ 对所有 }\ell\},
\qquad R\in G_{\mathcal Q}.
\tag{15.10a}
$$

任一 $Q^\ell$ 正定且 $V$ 可逆，使同数据的 $WQ^\ell W^{\mathsf T}$ 正定，故 $W$ 也可逆。将 $WQ^\ell W^{\mathsf T}=VQ^\ell V^{\mathsf T}$ 左右乘以 $V^{-1}$、$V^{-\mathsf T}$ 即得上述等价变形。因此该共同合同稳定子若为 $\{I,-I\}$，即使菜单不完整也能识别全部帧至共同符号；同源带符号锚再固定该符号。此判据限定于可逆方帧，不冒充任意退化矩阵的分类。

一个严格的不完整例子是 $m=3$、$V=I_3$，以及实际许可的三个正定协方差

$$
Q^1=I_3,\qquad Q^2=\operatorname{diag}(1,2,3),\qquad
Q^3=I_3+uu^{\mathsf T},\qquad u=(1,1,1)^{\mathsf T}.
\tag{15.10b}
$$

它们只有三维线性张成，未张成六维 $\operatorname{Sym}_3$。若 $WQ^\ell W^{\mathsf T}=Q^\ell$，第一式迫使 $W$ 正交，第二式迫使它与具有不同特征值的 $Q^2$ 交换，故 $W=\operatorname{diag}(s_1,s_2,s_3)$、$s_i\in\{\pm1\}$。第三式给 $s_is_j=1$ 对全部 $i,j$，所以 $W=\pm I_3$。于是 $T_{11}=E_{11}$ 也由这些数据唯一确定，尽管 $E_{11}\notin M$：若 $E_{11}=\alpha I+\beta Q^2+\gamma Q^3$，非对角项先给 $\gamma=0$，第 2、3 个对角项再给 $\alpha=\beta=0$，与第 1 项矛盾。

上述例子可放在 (16.9) 的同一个线性来源和投影上，取常值投影帧 $V=I_3$ 和同一有符号坐标校准；三个设置只改变 $Q$，不更换来源或标签。它证明完整张成不是非线性识别的必要条件。反之，单个正定 $Q$ 的共同合同稳定子为 $Q^{1/2}O(m)Q^{-1/2}$；在 $m\ge2$ 的可逆方帧类中，它一般保留标签混合歧义，命题 17.1 给出同纤维的实际例子。最后，任意菜单均在共同换号下不变，故不能单凭协方差消除 (15.10)。证毕。以上是精确数据的识别结论，未给出有限精度的稳定性或取得这些矩率的费用；它们仍须原取得合同。定理不把一个二阶括号、一个统计连接或一条投影扩散律变成新的原生控制。

**命题 15.5（受限来源与不连通纤维）。** 若 $F_y$ 不连通，令 $\mathscr C_y=\pi_0(F_y)$。在完整菜单和第 1 项下，对每个 $C\in\mathscr C_y$ 存在 $\epsilon_{y,C}\in\{\pm1\}$，使

$$
d\Pi X_a|_C=\epsilon_{y,C}\,v_a(y),
\tag{15.11}
$$

其中 $v_a(y)$ 是任一选定分支的向量；共同漂移的投影则是依赖分支的量 $v_0(y,C)$。因此 $K$ 上的带标签商存在，当且仅当对每个 $y$ 所有分支的 $\epsilon_{y,C}v_a(y)$（每个 $a$）相等，并且所有 $v_0(y,C)$ 相等；再加上各分支的符号锚相容。充分性由把这些共同值定义为 $\overline X_a(y)$、$\overline X_0(y)$，并重复定理 15.3 的证明得到。

若这些相等式失败，精确商只能取为 $\widetilde B=\{(y,C):C\in\mathscr C_y\}$ 或保留相应的分支标签。不能以总空间连通、一个协方差值或一个代表分支替代这些条件。特别地，一个有限样本的同值读数不证明 (15.11) 在未读的来源分支上成立。

## 16. 距离、实际路径与同一时钟的二阶传播

**假设 16.1（旧距离和控制合同）。** 沿用 §10 的全域二次距离律

$$
d_D(x,x')^2=g_D(x-x',x-x')
=\langle\Pi x-\Pi x',\Pi x-\Pi x'\rangle_K.
\tag{16.1}
$$

一个实际确定性控制 $u=(u_1,\ldots,u_m)$ 是分段 $C^1$；控制合同还要求在声明的有限时段内存在唯一完整提升 $z:[0,T]\to S$，并满足

$$
\dot z(t)=\sum_{a=1}^m u_a(t)X_a(z(t)),
\tag{16.2}
$$

在所有时刻通过守卫。若合同把共同漂移也作为确定性执行的一部分，则在 (16.2) 右端另加 $X_0(z(t))$；下文始终明确采用哪一种时钟和方程。实际成本是合同给出的

$$
\operatorname{Cost}(u,z)=\int_0^T c(u(t),z(t))\,dt,
\tag{16.3}
$$

它包含同时控制的费用、守卫、源服务、保留和失败收费；投影不会删除任何一项。

**定理 16.2（旧距离的精确消费与路径提升）。** 在定理 15.3 和假设 16.1 下，每个有限实际路径的投影 $y=\Pi\circ z$ 满足

$$
\dot y(t)=\sum_a u_a(t)\overline X_a(y(t)),
\qquad
d_D(z(s),z(t))=\|y(s)-y(t)\|_K.
\tag{16.4}
$$

若固定初点 $z(0)$ 和一条满足该完整性合同的合法控制 $u$，则 (16.2) 的提升在其源寿命内唯一，故 (16.4) 对所有 $0\le s,t\le T$ 同时成立。若要由解析条件推出该合同，可另加 $X_a$ 在声明源域上的线性增长和守卫闭合；局部光滑性单独不排除有限时间爆炸。旧距离任务在终点上的值恰为 $\|y(T)-y(0)\|_K$；实际控制成本仍是 (16.3)，不等同于该欧氏距离。不同隐藏初点的提升可以有不同的完整记录而有同一个 $y$ 路径。

证明。链式法则和 (15.4) 给出第一式。把 $z(t)-z(s)$ 代入 (16.1) 给第二式；它是同一来源的精确度量律。局部光滑性给出提升的局部唯一性；完整提升和守卫由控制合同承担（或由上述线性增长条件推出）。长度和费用的区分由 (16.3) 的定义直接保持。证毕。

**假设 16.3（同一时钟的扩散合同）。** 取菜单中的一个 $Q$，令 $W$ 为协方差 $Q$ 的布朗运动。沿用定理 15.3 的实际场、来源和投影。本合同以 $S,B$ 的内部为生存域，仍记为 $S,B$；碰边界时杀死，边界初点的寿命为零。以下解析条件须对每个拟消费的菜单成员分别成立。

使用 $J$ 原有正定内积的范数控制爆炸，不替代 $g_D$ 或 $K$ 的旧度量。要求源场及其已下降的基场分别有全空间 $J,K$ 上的光滑延拓。下列全空间估计中的场指这些延拓，在生存域内仍是原实际场。延拓只用于构造直到退出的解，不授予域外操作权限。对 $H=J,K$，分别令 $U_i^J=X_i$、$U_i^K=\overline X_i$，定义实际 Itô 漂移和噪声矩率

$$
b_Q^H(u)=U_0^H(u)+\frac12\sum_{a,b}Q_{ab}
DU_b^H(u)\,U_a^H(u),
\qquad
a_Q^H(u)=\sum_{a,b}Q_{ab}
\langle U_a^H(u),U_b^H(u)\rangle_H.
\tag{16.5a}
$$

要求存在常数 $C_Q^H\ge0$，使在各自全空间上

$$
2\langle u,b_Q^H(u)\rangle_H+a_Q^H(u)
\le C_Q^H(1+\|u\|_H^2).
\tag{16.5b}
$$

这是对实际 Itô 生成元的径向估计。一个更强的充分条件是 $b_Q^H$ 和 $U_a^H$ 都线性增长；仅 $U_0^H,\ldots,U_m^H$ 线性增长不控制 (16.5a) 中的导数修正。

对任意完整连续源路径 $z_\cdot$，记 $\tau_S(z)=\inf\{t\ge0:z_t\notin S\}$，基域同样定义。令 $\widetilde Z$ 表示未杀死的全空间源解；要求对每个源初点，几乎必然有

$$
\tau_S(\widetilde Z)=\tau_B(\Pi\widetilde Z).
\tag{16.5}
$$

这是原源守卫与投影守卫的匹配条件。若原守卫已满足 $S=\Pi^{-1}(B)$，该等式逐连续路径成立；一般受限来源须另证，不能删掉隐藏守卫以制造匹配。所需全空间解的存在由 (16.5b) 及下述证明给出，故 (16.5) 不预设一个未经建立的非爆炸结论。源 SDE 采用原时钟

$$
dZ_t=X_0(Z_t)\,dt+\sum_aX_a(Z_t)\circ dW_t^a.
\tag{16.6}
$$

**定理 16.4（全起点有限时间的同一时钟传播）。** 在定理 15.3 和假设 16.3 下，对每个 $z\in S$，源与基的全空间辅助解在每个有限时间窗均不爆炸。实际源解为它在 $\tau_S$ 杀死的唯一强解，并且 $Y_t=\Pi(Z_t)$ 在生存时是唯一解

$$
dY_t=\overline X_0(Y_t)\,dt
+\sum_a\overline X_a(Y_t)\circ dW_t^a
\tag{16.7}
$$

直到 $\tau_B=\tau_S$。两者在死亡时均送入同一个吸收墓地 $\dagger$，约定 $\Pi\dagger=\dagger$、$\varphi(\dagger)=0$。这里的非爆炸性逐起点成立，不声称存在一个对全部不可数起点通用的零测集。对任意有界 Borel 函数 $\varphi$、任意 $t\ge0$，

$$
\mathbb E_z[\varphi(\Pi Z_t)\mathbf1_{t<\tau_S}]
=\mathbb E_{\Pi z}[\varphi(Y_t)\mathbf1_{t<\tau_B}]
:=P_t^B\varphi(\Pi z).
\tag{16.8}
$$

所以 $(P_t^B)_{t\ge0}$ 是同一原时钟中的杀死扩散半群；(16.8) 是全有限时间的路径和半群陈述，不只是一个生成元恒等式。无有限边界退出时，实际寿命为无穷；有边界时，寿命由 (16.5) 的共同退出决定，有限时间的无穷远爆炸已由 (16.5b) 排除。不同全空间延拓在退出前给出同一个解。

证明。先分别在 $H=J,K$ 上构造未杀死解。把 $W$ 写成 $Q^{1/2}\beta$，其中 $\beta$ 为标准布朗运动，则 Itô 方程的漂移恰为 (16.5a)，扩散列为 $\sum_aU_a^H(Q^{1/2})_{aj}$。光滑性给局部 Lipschitz；在每个球上截断为全局 Lipschitz 系数并用局部存在唯一性拼接，得到直到无穷远爆炸的最大强解。这一局部 SDE 事实参见 Hochgerner–Ratiu，Theorem 3.1；该定理本身只给直到爆炸的结论。

记 $V_H(u)=1+\|u\|_H^2$，$\rho_R=\inf\{t:\|U_t\|_H\ge R\}$，其中 $R>\|U_0\|_H$。对截断解应用停止的 Itô 公式，球内的随机积分期望为零；(16.5b) 和 Gronwall 不等式给

$$
\begin{aligned}
\mathbb E V_H(U_{t\wedge\rho_R})
&\le V_H(U_0)+C_Q^H\int_0^t
\mathbb E V_H(U_{s\wedge\rho_R})\,ds
\le V_H(U_0)e^{C_Q^Ht},\\
\mathbb P(\rho_R\le T)
&\le\frac{V_H(U_0)e^{C_Q^HT}}{1+R^2}
\longrightarrow0.
\end{aligned}
\tag{16.8a}
$$

因此任意固定起点在每个有限 $T$ 前爆炸的概率为零；对整数 $T$ 取可数并即得全寿命存在。此论证在源和基上分别成立，不用 Stratonovich 场的线性增长代替导数估计。

在同一 $W$ 上耦合源解 $\widetilde Z$ 与从 $\Pi z$ 开始的基解 $\widetilde Y$。在任一解退出前，Stratonovich 链式法则及 (15.4)、(15.7) 给 $\Pi\widetilde Z$ 满足 (16.7)。以两个退出时刻的较小者局部化，路径唯一性给两路径在该时刻前相等；连续性和 (16.5) 排除一个先于另一个退出。因此 $\tau_S=\tau_B$，两路径直到共同死亡相等，此后均为 $\dagger$。这逐路径给出 (16.8)，包括所有有界 Borel 函数，无须用生成元恒等式推断寿命。局部唯一性还说明更换域外延拓不改变退出前路径或退出时刻。

系数和生存域不随时间改变。强解唯一性及布朗增量的 Markov 性说明，在 $s<\tau_B$ 条件下，随后 $t$ 时长的杀死期望为 $P_t^B\varphi(Y_s)$；死亡后该量为零。取期望即得 $P_{s+t}^B=P_s^BP_t^B$。方程保留同一个 $Q$、$1/2$ 归一化、时钟、守卫、隐藏记录和源寿命；既未重新采样来源，也未赋予额外控制。证毕。

**模型 16.5（有真实隐藏记录的正模型）。** 取

$$
J=\mathbb R^3\times\mathbb R^2,
\quad K=\mathbb R^3,
\quad\Pi(q,h)=q,
\quad g_D((q,h),(q',h'))=q\cdot q'.
\tag{16.9}
$$

令 $e'_1,e'_2$ 是隐藏因子的标准基，取全局光滑且线性增长的 $b(q)=Aq+c$，以及

$$
X_0(q,h)=(b(q),-\lambda h),\quad
X_1=(e_1,e'_1),\quad X_2=(e_2,e'_2),\quad X_3=(e_3,0),
\quad \lambda>0.
\tag{16.10}
$$

任意完整的正定菜单满足 (15.2)，并取显示的有符号坐标校准；投影条件由常系数控制直接满足，且 $\overline X_0=b$、$\overline X_a=e_a$。取 $S=J$、$B=K$，两退出时刻均为无穷。在 $J$ 上取标准乘积范数。控制场的导数为零，所以 $b_Q^J=(Aq+c,-\lambda h)$、$b_Q^K=Aq+c$，而 $a_Q^J=2Q_{11}+2Q_{22}+Q_{33}$、$a_Q^K=\operatorname{tr}Q$。由 $2q\cdot c\le\|q\|^2+\|c\|^2$ 和 $2q\cdot Aq\le2\|A\|\|q\|^2$，(16.5b) 对两空间均成立，例如可共同取 $C_Q=2\|A\|+1+\|c\|^2+2Q_{11}+2Q_{22}+Q_{33}$。这给出定理 16.4 的一个全起点消费者。

初始记录 $(q,h)$ 与 $(q,\widetilde h)$ 在 $h\ne\widetilde h$ 时是真正不同的来源记录；$h$ 还受漂移和前两个实际控制改变。取锚列 $h_1=(e_1,0),h_2=(e_2,0),h_3=(e_3,0),h_4=(0,e'_1),h_5=(0,e'_2)$ 即得到张成 $J$ 的同源有限标定列。三维距离、二阶传播和五维隐藏记录在同一个 $J$ 上共存；模型没有声称隐藏坐标是物理空间，也没有把投影变成对 $h$ 的取得权限。

## 17. 分离反模型与可证伪边界

**命题 17.1（单一协方差律不固定命名控制）。** 取 $S=\mathbb R^3\times S^1$、$\Pi(q,\theta)=q$，在 $e_1e_2$ 平面令 $R_\theta$ 为旋转，定义

$$
X_1=(R_\theta e_1,0),\quad
X_2=(R_\theta e_2,0),\quad X_3=(e_3,0),\quad X_0=0.
\tag{17.1}
$$

对唯一介入 $Q=I_3$，投影协方差恒为 $I_3$，所以投影扩散律不依赖 $\theta$；但同名的 $X_1$、$X_2$ 随纤维改变。证明是 $R_\theta(e_1e_1^{\mathsf T}+e_2e_2^{\mathsf T})R_\theta^{\mathsf T}=e_1e_1^{\mathsf T}+e_2e_2^{\mathsf T}$。完整菜单正是为排除这一标签旋转而要求的额外信息。

**命题 17.2（不连通纤维的标签逃逸）。** 取 $S=\mathbb R^3\times\{-1,+1\}$、$\Pi(q,\sigma)=q$，并令 $X_a(q,\sigma)=(\sigma e_a,0)$、$X_0=0$。对每个协方差 $Q$，

$$
\sum_{a,b}Q_{ab}\,d\Pi X_a\otimes d\Pi X_b=Q
\tag{17.2}
$$

在两个分支相同；但标签 $a$ 的有向控制在两个分支相反。这里每个分支的菜单证书都有一个符号，然而 $\epsilon_{y,+}=-\epsilon_{y,-}$，故命题 15.5 的兼容性失败。只保留 $q$ 的协方差和距离不能把两个分支压成带标签的 $K$ 商。

**命题 17.3（手性与隐藏漂移的两个独立失败）。**

1. 在连通 $S=\mathbb R^3\times\mathbb R$ 上，模型 A 取 $X_a=(e_a,0)$，模型 B 取 $X_a=(-e_a,0)$，两者 $X_0=0$。任意完整协方差菜单的所有二阶张量相同，但同名控制的方向相反；没有实际有符号锚时，(15.10) 不能被消除。
2. 取 $S=\mathbb R^3\times\mathbb R$、$X_a=(e_a,0)$，而 $X_0(q,h)=(h e_1,0)$。所有协方差读数和全部控制场相同，但漂移 $d\Pi X_0=h e_1$ 随纤维变化；投影扩散的漂移因而不是 $K$ 上的单值函数。任何只检查二阶矩率而不检查 (15.7) 的证书都会错误通过。

证明。第 1 项由 $(-v_a)\otimes(-v_b)=v_a\otimes v_b$；第 2 项由 $\Gamma_Q$ 不含 $X_0$ 且 (15.7) 在 $h\ne\widetilde h$ 时失败。两项都满足相同的正定性和光滑性，故失败不是退化或不连续造成的。证毕。

**命题 17.4（有限读取不能替代全源条件）。** 对任意有限的读取点集 $E\subset S$，存在两个光滑控制系统，它们在 $E$ 上的全部菜单矩率、漂移和校准值相同，而在 $S\setminus E$ 上的带标签运输不同。取一个不在 $E$ 上的光滑紧支撑函数 $\chi$，把一个控制的投影场从 $e_1$ 改为 $e_1+\chi e_2$ 即可；若需要保持有限点的全部二阶读数，则让 $\chi$ 在这些点的邻域恒为零。故有限精度和有限采样不能认证“所有来源纤维”的精确证书；一个有限菜单也不是在无界来源上只取有限观察。

同样，实测频率是有限样本的获取结果，$\Gamma_Q$ 是假设的精确矩率。前者可用于统计误差合同，不能把一个近似相等升级为 (15.5) 的全域恒等式。若同一来源的新读取发现 $T_{ab}$、漂移残差、守卫或死亡时间在同一 $\Pi$ 纤维的两个代表上不同，证书立即被否证；若发现锚的有向读数相反，则否证的是带标签版本而非无向协方差版本。

**命题 17.5（有界 Stratonovich 控制仍可有限时间爆炸）。** 在 (16.9) 的同一个 $J,K,\Pi,g_D$ 上取 $S=J$、$B=K$，写 $q=(x,y,z)$，并令

$$
\begin{aligned}
\theta(q)&=xy^2,&
V_1(q)&=(\cos\theta,\sin\theta,0),&
V_2(q)&=(-\sin\theta,\cos\theta,0),\\
X_1(q,h)&=(V_1(q),e'_1),&
X_2(q,h)&=(V_2(q),e'_2),&
X_3(q,h)&=(e_3,0),&
X_0(q,h)&=(0,-\lambda h),\quad\lambda>0.
\end{aligned}
\tag{17.3}
$$

这些控制光滑且有界，漂移线性增长，纤维是连通的 $\mathbb R^2$，全部场已通过同一 $\Pi$ 下降。实际带符号锚可取 $\widehat v_1=V_1$ 及其欧氏对偶，锚读数恒为 $1$。令实际许可的完整菜单为 $I$、$I+E_{11}$、$I+E_{22}$ 和 $I+(E_{ij}+E_{ji})/2$、$1\le i<j\le3$；它们正定且张成 $\operatorname{Sym}_3$。所有菜单生成元均为基本的，故 §15 的识别条件不能排除此模型。有限分段 $C^1$ 控制的确定性路径也完整：$q$ 的速度被 $\sum_a|u_a|$ 控制，$h$ 满足线性受迫方程。但 $Q=I$ 的同一原时钟扩散从某些起点以正概率在有限时间爆炸。

证明。对旋转角的任意光滑函数 $\theta$，直接微分给

$$
\frac12\bigl((DV_1)V_1+(DV_2)V_2\bigr)
=\frac12(-\partial_y\theta,\partial_x\theta,0)
=(-xy,y^2/2,0).
\tag{17.4}
$$

因此基的 Itô 漂移为 $(-xy,y^2/2,0)$，扩散协方差为 $I_3$。对驱动的前两个分量作沿解的适应正交旋转，其积分是布朗运动 $\beta$；在最大寿命后以单位旋转延拓该积分仍为布朗运动。第二坐标在寿命前满足

$$
Y_t=4+\beta_t^2+\frac12\int_0^tY_s^2\,ds
\tag{17.5}
$$

当 $Y_0=4$ 时，事件 $\inf_{0\le s\le1}\beta_s^2\ge-1$ 的概率由布朗反射原理为 $2\Phi(1)-1>0$，其中 $\Phi$ 为标准正态分布函数。在此事件上、只要有限解仍存在，令 $v(t)=3+\frac12\int_0^tY_s^2ds$，则 $Y_t\ge v(t)>0$ 且 $v'\ge v^2/2$，故 $v(t)\ge3/(1-3t/2)$ 对 $t<2/3$ 成立。若解活过 $2/3$，连续性将与这个发散下界矛盾，因此最大寿命至多为 $2/3$。源的隐藏坐标是线性方程，不会消除此爆炸；源和基均无有限边界可用于解释它。

模型不满足 (16.5b)：在基的 $x=z=0$、$y\to+\infty$ 上，其左侧为 $y^3+3$。这也显示新增估计确实检验了一个未由光滑性、有界噪声、完整菜单、定向和生成元投影保证的条件。对已声明的 $C_Q^H$，一个精确违例即否证该常数下的合同；有限点通过不认证全空间估计，有限精度读数只能按其误差合同排除候选。证毕。

**命题 17.6（非爆炸不替代守卫匹配）。** 在同一 $J,K,\Pi,g_D$ 上取受限来源 $S=\mathbb R^3\times(-1,1)\times\mathbb R$，$B=\mathbb R^3$，控制仍为 (16.10) 的三个常场，但令 $X_0=0$。用相同完整菜单和有符号校准，全部场可下降，且常系数全空间延拓满足 (16.5b)。然而，按原隐藏守卫杀死源不能得到无边界基过程的 (16.8)。

证明。取 $Q=I$ 和隐藏第一坐标初值 $0$，则源的该坐标等于 $W_t^1$，源死亡时刻为 $\tau_S=\inf\{t:|W_t^1|\ge1\}$。基过程是三维布朗运动且 $\tau_B=\infty$。对每个 $t>0$，事件 $|W_t^1|\ge1$ 有正概率并蕴含 $\tau_S\le t$，故以 $\varphi=1$ 比较时，源侧期望 $\mathbb P(\tau_S>t)<1$，基侧为 $1$。因此 (16.5) 是独立条件；常系数、同钟、非爆炸和精确局部生成元均不能删除它。证毕。

## 18. 来源、复用与边界

本增补的有限菜单重建是对第 10 节同源商的一个源特定消费者：它使用协方差张成 $\operatorname{Sym}_m$、纤维连通性或显式分支兼容性，以及一份实际带符号校准。它没有把一般的 projectability、Frobenius 条件、joint diagonalization 或统计投影联络单独包装成新结果。

Elworthy–Le Jan–Li, *The Geometry of Filtering*, arXiv:0810.2253v1，引言关于 symbol 投影的说明、§1.4 Proposition 1.4.4 及第 2 章式 (2.3) 供应扩散算子、symbol 和光滑映射之间的标准关系。Hochgerner–Ratiu, *Geometry of non-holonomic diffusion*, arXiv:1204.6438v1, Theorem 3.1（PDF 第 21 页）只供应直到爆炸的存在唯一性，随后第 22 页给出联络漂移 $X_0+\frac12\sum_a\nabla_{X_a}X_a$；Theorem 3.2（第 24--25 页）区分 Stratonovich 算子本身的可投影性与扩散及生成元的可投影性。(16.5a) 在同一线性坐标和协方差 $Q$ 上使用该标准修正，(16.8a) 另以停止的 Itô 公式证明非爆炸；(16.5) 另承担原守卫匹配。(16.7)--(16.8) 因而保留了带标签场、原时钟和完整源寿命，不从局部生成元投影单独推断这些结论。Kleinsteuber–Shen, *Uniqueness Analysis of Non-Unitary Matrix Joint Diagonalization*, arXiv:1111.7088v3, Theorems 1--3（尤其 Theorem 1 的 essential uniqueness 条件）是多矩阵二阶识别的成熟背景；推论 15.4 使用共同合同稳定子的直接计算，未把线性张成等同于非线性可识别性，也不声称复制其算法或全部模型。

仓内复用边界如下。[可取得预测丛卷](AURIC_FIB_OBTAINABLE_PREDICTIVE_BUNDLE_THEORY.md) §1 和命题 2.13 把精确秩、条件数和取得资源分开；[二次时钟卷](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md) §11 保留原风险和标定；[相对测量卷](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) §§15--16 把有限记录、确定性/置信界和 bit time、workspace、output、backing 分开。[FIB 原生自由扩散卷](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md) §§1--3 已给实际原生 rank-two 场、守卫、密度和完整 killed-semigroup 条件；[概率相位卷](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md) §10.4--§10.5 的两控制 principal-symbol 障碍不能因本节的抽象菜单而取得第三个原生噪声方向。[递归边界卷 Continuation III](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md) §§81--83 的同源空间/Green 要求和三维 Brownian factor、[Continuation IX](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IX.md) §§243--246 的 affine holonomy 与局部三框架到整体载体条件，分别是边界条件和整体运输的既有供应者；本节只在 (15.1)--(16.10) 的明确同源合同上消费它们。所有这些引用仍是理论来源或仓内综合，不是本节的 Lean 认证，也不产生原生 FIB 的实际控制、取得、未知环境维数、无限时间稳定性或物理实现。

本批的结论范围是：在完整有限协方差菜单、带符号校准、来源守卫、光滑性、(16.5b) 所保证的非爆炸性和 (16.5) 的同一死亡时钟这些明确条件下，三轴任务商同时成为每个实际命名控制和共同漂移的精确商，并给出 (16.4)、(16.8) 的距离与传播对应。完整张成是线性重建的充分条件，非线性识别可用更小菜单；对应的精确例子见推论 15.4。标签旋转、分支、定向、漂移和有限读取的边界见命题 17.1--17.4；无穷远爆炸与隐藏守卫的独立失败见命题 17.5--17.6。以上条件既不证明物理实现、无限时间稳定性，也未解决“为什么宇宙是三维”或 native FIB 的控制取得问题。

## 追加锚（本行以下为增补区）

## 19. 任意交错积的定量 Jacobi 下界与等号刚性

**定义 19.1（同一欧氏度量中的两个极值）。** 设 $V$ 为有限维实正定内积空间，$d=\dim V\ge4$，$B:V\times V\to V$ 双线性，且
$T(u,v,w)=\langle B(u,v),w\rangle$ 精确完全交错。所有范数、正交性、伴随和体积均取自这个给定内积。记

$$
A(u,v)=\|u\|^2\|v\|^2-\langle u,v\rangle^2,
\qquad
\mathcal J_B(u,v,w)=B(u,B(v,w))+B(v,B(w,u))+B(w,B(u,v)),
$$

$$
m(B)=\min_{\substack{\|u\|=\|v\|=1\\\langle u,v\rangle=0}}
       \|B(u,v)\|^2,
\qquad
j(B)=\max_{\|u\|=\|v\|=\|w\|=1}\|\mathcal J_B(u,v,w)\|. \tag{19.1}
$$

第二个极值的三个单位输入彼此独立，不附加正交条件。两个极值均由非空紧集上的连续函数取得。取四元数 $\mathbb H$ 的正交单位基 $(1,i,j,k)$，约定
$i^2=j^2=k^2=-1$、$ij=k$、$jk=i$、$ki=j$，反向乘积变号；$\bar x$ 表示四元数共轭。在正交直和 $\operatorname{Im}\mathbb H\oplus\mathbb H$ 上定义

$$
C((p,x),(q,y))=
\bigl(p\times q+\operatorname{Im}(x\bar y),\,-py+qx\bigr),
\qquad p\times q=\frac{pq-qp}{2}. \tag{19.2}
$$

这里直和内积为
$\langle(p,x),(q,y)\rangle=p\mathbin{\cdot}q+\operatorname{Re}(x\bar y)$。

**定理 19.2（任意积的齐次定量界及全部等号情形）。** 在定义 19.1 下，若 $m(B)>0$，则

$$
d=7,\qquad j(B)\ge3m(B). \tag{19.3}
$$

等号 $j(B)=3m(B)$ 成立，当且仅当存在正交同构
$U:\operatorname{Im}\mathbb H\oplus\mathbb H\to V$，使对全部 $u,v\in V$ 有

$$
B(u,v)=\sqrt{m(B)}\,U C(U^{-1}u,U^{-1}v). \tag{19.4}
$$

**证明。** 记 $m=m(B)>0$、$\sigma=\sqrt m$。完全交错性和内积非退化性给出

$$
B(u,v)=-B(v,u),\qquad B(u,v)\perp u,v,
\qquad L_u^*=-L_u,\quad L_uv=B(u,v). \tag{19.5}
$$

先说明维数供应者的适用性。若 $a,b$ 线性无关，置
$b_\perp=b-\langle b,a\rangle a/\|a\|^2$。则 $b_\perp\ne0$，且

$$
B(a,b)=B(a,b_\perp),\qquad
\|B(a,b)\|\ge\sigma\|a\|\|b_\perp\|>0. \tag{19.6}
$$

Draisma–Shaw, *Some noteworthy alternating trilinear forms*,
[arXiv:1102.4768v1](https://arxiv.org/html/1102.4768v1)，定义 (2) 与 Theorem 2，说明在实维数 $d>2$ 且 $d\notin\{3,7\}$ 时，每个交错三形式都有奇异射影直线；其确切含义是存在独立 $a,b$，使 $T(a,b,x)=0$ 对全部 $x$ 成立。在本题给定的同一非退化内积中，这等价于 $B(a,b)=0$，与 (19.6) 矛盾。因此 $d\ge4$ 的全部可行情形均有 $d=7$。这里只复用该经典维数排除结论；尚未对 $B$ 增加精确范数恒等式。

（一）极小对导出的不变三平面。取达到 $m$ 的正交单位对 $u,v$，置 $c_*=B(u,v)$。对任意 $h\perp u,v$，以
$u(t)=(u+th)/\sqrt{1+t^2\|h\|^2}$ 变分，极小性给

$$
0=\langle B(h,v),c_*\rangle
 =\langle B(v,c_*),h\rangle.
$$

故 $B(v,c_*)\in\operatorname{span}\{u,v\}$。由交错性，其 $v$ 系数为零，而
$\langle B(v,c_*),u\rangle=T(v,c_*,u)=\|c_*\|^2=m$。
对 $v$ 作同样的受约束变分，则
$\langle B(u,h),c_*\rangle=\langle B(c_*,u),h\rangle=0$，从而

$$
B(v,c_*)=mu,\qquad B(c_*,u)=mv. \tag{19.7}
$$

于是 $e_1=u,e_2=v,e_3=c_*/\sigma$ 是某个三平面 $E$ 的定向正交单位基，且

$$
B(a,b)=\sigma\,a\times_E b\quad(a,b\in E). \tag{19.8}
$$

令 $W=E^\perp$，则 $\dim W=4$。对 $a\in E,x\in W,b\in E$，有
$\langle B(a,x),b\rangle=-\langle x,B(a,b)\rangle=0$。
因此 $A_ax=B(a,x)$ 将 $W$ 保持在自身内，且为斜伴随算子。由 $a\perp x$ 和 $m$ 的定义，齐次性给出

$$
\|A_ax\|\ge\sigma\|a\|\|x\|\qquad(a\in E,\ x\in W). \tag{19.9}
$$

三平面及此一致下界均由极小性导出。

（二）四维斜算子的两项分解。将 $W$ 等距识别为 $\mathbb H$。对虚四元数 $p,q$，记
$L_px=px$、$R_qx=xq$。两类算子均斜伴随，各成三维线性子空间，且交为零：若 $L_p=R_q$，代入 $1$ 得 $p=q$，再代入任意 $x$ 得 $p$ 与所有四元数对易，故虚部 $p=0$。由于 $\dim\mathfrak{so}(4)=6$，存在唯一线性映射
$P,Q:E\to\operatorname{Im}\mathbb H$，使

$$
A_a=L_{Pa}+R_{Qa}. \tag{19.10}
$$

当 $\|x\|=1$ 时，右乘 $x^{-1}$ 保范，故
$\|px+xq\|=|p+xqx^{-1}|$。单位四元数共轭在给定半径的虚球面上传递作用：虚单位 $n,m$ 且 $m\ne-n$ 时，非零的 $r=1-mn$ 满足 $rn=mr$；若 $m=-n$，可取与 $n$ 正交的虚单位 $r$。将 $r$ 单位化即得所需共轭。因此三角界的两个端点都可取到，包括某一虚部为零的情形，且

$$
\min_{\|x\|=1}\|(L_p+R_q)x\|=\bigl||p|-|q|\bigr|,
\qquad
\|L_p+R_q\|_{\rm op}=|p|+|q|. \tag{19.11}
$$

(19.9) 给 $\bigl||Pa|-|Qa|\bigr|\ge\sigma\|a\|$。
在 $E$ 的单位球面上连续函数 $|Pa|-|Qa|$ 不为零，球面连通使其符号恒定。若符号为负，以 $x\mapsto\bar x$ 改换 $W$ 的等距识别，则
$\overline{p\bar x+\bar xq}=-qx-xp$，将两项交换并变号。因此可以且以下固定为

$$
|Pa|-|Qa|\ge\sigma\|a\|\qquad(a\in E). \tag{19.12}
$$

特别地，$P$ 的每个奇异值至少为 $\sigma$。

（三）由非奇异性确定定向。在上述定向基中，记 $e^r$ 为 $E$ 的对偶基，$e^{123}=e^1\wedge e^2\wedge e^3$，令
$\omega_r(x,y)=\langle A_{e_r}x,y\rangle$。由于 $T(E,E,W)=0$，完整的三形式恰有分解

$$
T=\sigma e^{123}+\sum_{r=1}^3e^r\wedge\omega_r+\rho,
\qquad \rho\in\Lambda^3W^*. \tag{19.13}
$$

这里 $\rho$ 任意，并未删除 $W$ 上的三次项。设 $(\theta^0,\theta^1,\theta^2,\theta^3)$ 为 $(1,i,j,k)$ 的对偶基，固定

$$
\operatorname{vol}=e^{123}\wedge\theta^0\wedge\theta^1\wedge\theta^2\wedge\theta^3,
\qquad
\chi(z)\operatorname{vol}=\frac16(\iota_zT)\wedge(\iota_zT)\wedge T. \tag{19.14}
$$

对任意 $z\ne0$，$\omega=\iota_zT$ 在 $z^\perp$ 上非退化。事实上，若 $y\in z^\perp$ 且 $\omega(y,x)=0$ 对全部 $x\in z^\perp$ 成立，则 $B(z,y)$ 与 $z^\perp$ 正交，又由 (19.5) 与 $z$ 正交，所以 $B(z,y)=0$；(19.6) 或其正交齐次界迫使 $y=0$。令
$\eta=\langle z,\cdot\rangle/\|z\|^2$，则 $\eta(z)=1$，并可写
$T=\eta\wedge\omega+\rho_z$，其中 $\iota_z\rho_z=0$。在六维 $z^\perp$ 上，非退化性给 $\omega^3\ne0$，而水平七形式为零，故

$$
(\iota_zT)^2\wedge T=\eta\wedge\omega^3\ne0. \tag{19.15}
$$

上标表示楔幂。于是二次函数 $\chi$ 在连通的 $V\setminus\{0\}$ 上处处不为零且同号。

为确定该符号及 $P$ 的定向，写出 $L_i,L_j,L_k$ 对应的二形式：

$$
\theta^0\wedge\theta^1+\theta^2\wedge\theta^3,\qquad
\theta^0\wedge\theta^2-\theta^1\wedge\theta^3,\qquad
\theta^0\wedge\theta^3+\theta^1\wedge\theta^2.
$$

$R_i,R_j,R_k$ 的二形式分别将每式的第二项变号。这六个式子直接给出 $L_p+R_q$ 对应的二形式 $\omega_{p,q}$ 满足

$$
\omega_{p,q}^2=2(|p|^2-|q|^2)
\theta^0\wedge\theta^1\wedge\theta^2\wedge\theta^3. \tag{19.16}
$$

由 $\iota_{e_1}T=\sigma e^2\wedge e^3+\omega_1$，(19.13) 的展开中仅留下
$3\sigma e^{123}\wedge\omega_1^2$，所以

$$
\chi(e_1)=\sigma(|Pe_1|^2-|Qe_1|^2)>0. \tag{19.17}
$$

再在 $1\in W$ 处求值。将虚四元数向量 $Pe_r+Qe_r$ 的欧氏对偶记为 $d_r$。在 $1^\perp=E\oplus\operatorname{Im}\mathbb H$ 上有

$$
\iota_1T=-\sum_{r=1}^3e^r\wedge d_r+\iota_1\rho,
\qquad
(\iota_1T)^3=6\det(P+Q)e^{123}\wedge\theta^1\wedge\theta^2\wedge\theta^3. \tag{19.18}
$$

含 $\iota_1\rho$ 的项至少含四个 $\operatorname{Im}\mathbb H$ 方向，故全为零；其余三项的重排符号给上式的正号。用 $\eta=\theta^0$ 代入 (19.15)，再把 $\theta^0$ 移过三个 $E$ 协向量，得到

$$
\chi(1)=-\det(P+Q)>0. \tag{19.19}
$$

因此 $\det(P+Q)<0$。对 $0\le t\le1$，(19.12) 给
$|(P+tQ)a|\ge|Pa|-t|Qa|\ge\sigma\|a\|$，故这些映射全部可逆，行列式符号不变，最终得

$$
\det P<0. \tag{19.20}
$$

这个符号来自给定度量下的非奇异性；(19.14) 没有以三形式诱导的新度量替换原内积。


（四）Jacobi 的定量下界。由 (19.20)，可以选 $E$ 的定向正交奇异基 $a_1,a_2,a_3$，以及 $\operatorname{Im}\mathbb H$ 的定向正交基 $f_1,f_2,f_3$，使

$$
Pa_1=\lambda_1f_1,\quad Pa_2=\lambda_2f_2,\quad
Pa_3=-\lambda_3f_3,\qquad
\lambda_1,\lambda_2,\lambda_3\ge\sigma,\quad f_1\times f_2=f_3.
$$

左乘与右乘彼此对易，且四元数结合律给

$$
[L_p,L_r]=2L_{p\times r},\qquad
[R_q,R_t]=-2R_{q\times t}. \tag{19.21}
$$

右乘的负号来自 $R_qR_tx=x(tq)$。由于 $B(a_1,a_2)=\sigma a_3$，对 $x\in W$，Jacobi 三项按原次序相加恰为

$$
\begin{aligned}
\mathcal J_B(a_1,a_2,x)
&=([A_{a_1},A_{a_2}]-\sigma A_{a_3})x\\
&=\bigl(L_{(2\lambda_1\lambda_2+\sigma\lambda_3)f_3}
 +R_{-2(Qa_1\times Qa_2)-\sigma Qa_3}\bigr)x.
\end{aligned} \tag{19.22}
$$

对单位 $x\in W$ 取最大值，(19.11) 给出左右两项的算子范数之和，因而

$$
j(B)\ge2\lambda_1\lambda_2+\sigma\lambda_3
\ge3\sigma^2=3m. \tag{19.23}
$$

所有基变换均为原欧氏内积的等距变换。

（五）等号迫使全部剩余结构消失。若 $j(B)=3m$，(19.23) 和 $\lambda_r\ge\sigma$ 迫使
$\lambda_1=\lambda_2=\lambda_3=\sigma$。所以 $P/\sigma$ 为反定向等距映射，(19.12) 随即给 $Q=0$。以定向等距映射 $-P/\sigma$ 将 $E$ 识别为 $\operatorname{Im}\mathbb H$，便有

$$
B(p,q)=\sigma(p\times q),\qquad
B(p,x)=-\sigma px\quad(p,q\in E,\ x\in W). \tag{19.24}
$$

于是任意单位 $p\in E,x\in W$ 都是 $\|B(p,x)\|^2=m$ 的极小正交对。取任意 $y\in W\cap x^\perp$，以
$p(t)=(p+ty)/\sqrt{1+t^2\|y\|^2}$ 变分，得到

$$
0=\langle B(y,x),B(p,x)\rangle
=-\sigma\rho(y,x,px). \tag{19.25}
$$

对固定单位 $x$，映射 $p\mapsto px$ 将 $\operatorname{Im}\mathbb H$ 等距映到 $W\cap x^\perp$，故
$\rho(y,x,z)=0$ 对全部 $y,z\perp x$ 成立。任意 $y,z$ 可减去各自沿 $x$ 的分量，交错性使值不变，遂得 $\rho=0$。这也覆盖任意非零 $x$ 的齐次倍数，$x=0$ 时当然为零。

剩下的 $B(x,y)$ 属于 $E$，由交错性及 (19.24)，对任意虚四元数 $p$ 有

$$
\langle B(x,y),p\rangle
=\langle B(p,x),y\rangle
=-\sigma\operatorname{Re}(px\bar y)
=\sigma\langle p,\operatorname{Im}(x\bar y)\rangle.
$$

因此 $B(x,y)=\sigma\operatorname{Im}(x\bar y)$，连同 (19.24) 即为 (19.4)。等号分类的必要性由任意 $B$ 推出。

（六）模型恒等式及等号的反向。式 (19.2) 是经典虚八元数半交换子的一个正交表示；半交换子归一化参见 Baez, *The Octonions*, [§4.1](https://math.ucr.edu/home/baez/octonions/node14.html)。以下在本式的四元数约定中直接核对所需恒等式。$C$ 的三形式在 $E^3$ 上为普通体积，在 $E^2W$ 和 $W^3$ 上为零；混合分量满足

$$
\langle C(p,x),y\rangle=-\operatorname{Re}(px\bar y)
=\langle p,\operatorname{Im}(x\bar y)\rangle
=\langle p,C(x,y)\rangle.
$$

因 $\operatorname{Im}(y\bar x)=-\operatorname{Im}(x\bar y)$，这些分量精确完全交错。

置 $t=x\bar y$、$r=\operatorname{Re}t$、$a_0=p\mathbin{\cdot}q$。由
$pq=-a_0+p\times q$，有

$$
2\langle p\times q,\operatorname{Im}t\rangle
=-2\operatorname{Re}(pqt)-2a_0r.
$$

第二分量的平方为

$$
|-py+qx|^2=|p|^2|y|^2+|q|^2|x|^2
+2\operatorname{Re}(py\bar xq).
$$

实部的循环不变性和共轭不变性给
$\operatorname{Re}(py\bar xq)=\operatorname{Re}(qx\bar yp)=\operatorname{Re}(pqt)$。
这两个混合项相加恰为 $-2a_0r$。又
$|p\times q|^2=|p|^2|q|^2-a_0^2$，
$|\operatorname{Im}t|^2=|x|^2|y|^2-r^2$，所以对全部 $U=(p,x),V=(q,y)$ 有

$$
\begin{aligned}
\|C(U,V)\|^2
&=(|p|^2+|x|^2)(|q|^2+|y|^2)-(a_0+r)^2\\
&=\|U\|^2\|V\|^2-\langle U,V\rangle^2=A(U,V).
\end{aligned} \tag{19.26}
$$

因此 $m(C)=1$，且 $\|C(U,V)\|\le\|U\|\|V\|$。每个嵌套 Jacobi 项的范数至多为三个输入范数之积，故 $j(C)\le3$。对明确的单位三元组

$$
U=(i,0),\qquad V=(j,0),\qquad X=(0,1),
$$

内层积依次为 $C(V,X)=(0,-j)$、$C(X,U)=(0,i)$、$C(U,V)=(k,0)$，外层三项分别为

$$
C(U,C(V,X))=(0,k),\quad
C(V,C(X,U))=(0,k),\quad
C(X,C(U,V))=(0,k). \tag{19.27}
$$

故 $j(C)=3$。正交运输不改两个极值，正标量 $\sigma$ 则给
$m(\sigma C)=\sigma^2$、$\mathcal J_{\sigma C}=\sigma^2\mathcal J_C$、$j(\sigma C)=3\sigma^2$，证明等号分类的充分性。证毕。

## 20. 原全域预算的锐界、下确界与全部达到者

**定理 20.1（原分母和全参数域上的锐不等式）。** 对每个整数 $d\ge4$、每个实数 $0\le\alpha<1$、$\beta\ge0$，设 $V$ 为 $d$ 维实欧氏空间，$B:V\times V\to V$ 双线性，$T(u,v,w)=\langle B(u,v),w\rangle$ 精确完全交错。在同一给定欧氏内积和一个共同校准尺度下，若对全部 $u,v,w\in V$，包括零向量，均有

$$
\bigl|\|B(u,v)\|^2-A(u,v)\bigr|
\le\alpha\|u\|^2\|v\|^2,\qquad
\|\mathcal J_B(u,v,w)\|\le\beta\|u\|\|v\|\|w\|, \tag{20.1}
$$

则

$$
d=7,\qquad \beta\ge3(1-\alpha). \tag{20.2}
$$

这里面积残差的分母仍是 $\|u\|^2\|v\|^2$，并未改为 $A(u,v)$；Jacobi 输入也不要求正交。

**证明。** 在正交单位对上，(20.1) 给
$m(B)\ge1-\alpha>0$；在三个独立单位输入上，给 $\beta\ge j(B)$。故定理 19.2 适用，并给

$$
\beta\ge j(B)\ge3m(B)\ge3(1-\alpha).
$$

维数七是对所有 $d\ge4$ 的排除结论，非预设的子类限制。证毕。

**定义 20.2（原最优化及固定维数最优化）。** 对每个 $\alpha\in[0,1)$，令

$$
f(\alpha)=\inf\{\beta\ge0:\ \text{存在整数 }d\ge4\text{ 及满足定理 20.1 全部条件的 }(V,B)\}, \tag{20.3}
$$

空集下确界约定为 $+\infty$。将 $d$ 固定后的同一下确界记作 $f_d(\alpha)$。

**定理 20.3（全区间的值与穷尽达到分类）。** 对全部 $\alpha\in[0,1)$，可行集非空，且

$$
f(\alpha)=f_7(\alpha)=3(1-\alpha),\qquad
f_d(\alpha)=+\infty\quad(d\ge4,\ d\ne7). \tag{20.4}
$$

全域预算达到此下确界的资料恰为

$$
\beta=3(1-\alpha),\quad d=7,\quad
B(u,v)=\sqrt{1-\alpha}\,U C(U^{-1}u,U^{-1}v), \tag{20.5}
$$

其中 $U:\operatorname{Im}\mathbb H\oplus\mathbb H\to V$ 为任意正交同构。

**证明。** 固定 $\alpha\in[0,1)$，置 $\kappa=\sqrt{1-\alpha}$，在定义 19.1 的直和欧氏内积和同一校准尺度下取 $B=\kappa C$。由 (19.26)，对全部 $u,v$ 有精确残差

$$
\|B(u,v)\|^2-A(u,v)=-\alpha A(u,v),\qquad
0\le A(u,v)\le\|u\|^2\|v\|^2. \tag{20.6}
$$

故原面积预算在所有输入上成立，零向量和平行向量亦包括在内。由
$\mathcal J_B=\kappa^2\mathcal J_C$ 和 $j(C)=3$，原 Jacobi 预算以
$\beta=3(1-\alpha)$ 全域成立，(19.27) 的单位三元组取得该预算。张量交错性由 $C$ 的交错性继承。因此这是原条件的全域达到者，配合定理 20.1 的下界给出 (20.4)；固定非七维的可行集由同一定理为空。

反之，若某可行资料有 $\beta=3(1-\alpha)$，则

$$
3(1-\alpha)=\beta\ge j(B)\ge3m(B)\ge3(1-\alpha)
$$

迫使 $j(B)=3m(B)$ 和 $m(B)=1-\alpha$。定理 19.2 的等号分类遂精确给出 (20.5)。其每个正交运输由前段验证又都满足原条件并达到下确界，故分类穷尽。证毕。


## 21. 锐阈值下的原同源条件消费者

**假设 21.1（保留的来源、距离、标定和菜单条件）。** 采用假设 13.1 的共同实现，以下仅替换其代数维数阈值。具体保留如下条件。

1. $J$ 为有限维实内积空间，态域是整个 $J$；共同来源身份、来源版本、控制条件、校准尺度和共同零参照 $O$ 固定。真实同源差异 $h_1,\ldots,h_N$ 张成 $J$，$F:\mathbb R^N\to J$、$F\xi=\sum_j\xi_jh_j$。有对称双线性形式 $g_D$，在整个态域满足
   $d_D(x,y)^2=g_D(x-y,x-y)$、$d_D(x,y)\ge0$。同一组 $0,h_1,\ldots,h_N$ 按定义 2.1 构造的锚定 Gram 矩阵 $G$ 满足 $G\succeq0$，且由全域距离律有 $G_{jk}=g_D(h_j,h_k)$。取实际商载体
   $K=\mathbb R^N/\ker G$、$v_j=[\epsilon_j]$，内积为 $\langle[\xi],[\eta]\rangle_K=\xi^{\mathsf T}G\eta$，并保留定义 11.1 的 $d=\dim K\ge2$。
2. 在此同一个 $K$、此同一个内积和一个共同校准尺度上，有全域双线性 $B:K\times K\to K$，真实 $T(u,v,w)=\langle B(u,v),w\rangle_K$ 精确完全交错。真实积以非负预算 $\alpha,\beta$ 对全部输入满足原式 (11.1)–(11.2)，其分母、输入范围和归一化均不变。
3. $J$ 中有三个实际正交单位探针 $p_1,p_2,p_3$，读口为 $C_i(x)=\langle p_i,x\rangle_J$。在 $K$ 中选择正交单位 $a,b$，严格按有符号次序置

   $$
   c=B(b,a),\qquad s=\|c\|_K,\qquad e_1=a,\quad e_2=b,\quad e_3=c/s. \tag{21.1}
   $$

   在下述 $\alpha<1$ 条件下 $s>0$。对每个 $i$，选择形式系数 $\zeta_i$ 使 $[\zeta_i]=e_i$。保留全部精确同源距离—读出标定

   $$
   C_i(h_j)=\zeta_i^{\mathsf T}G\epsilon_j
   =\langle e_i,v_j\rangle_K
   \quad(i=1,2,3;\ j=1,\ldots,N). \tag{21.2}
   $$

4. 对菜单中包含的实际有序二元操作 $D:J\times J\to J$，每个方向读出 $\beta_i(x,y)=C_i(D(x,y))$ 为同一来源上的双线性函数，且保留全部精确标定

   $$
   \beta_i(h_j,h_k)=\langle e_i,B(v_j,v_k)\rangle_K
   \quad(i=1,2,3;\ j,k=1,\ldots,N). \tag{21.3}
   $$

   若该操作不在菜单中，省去此项及二元操作结论；不因此给 $D$ 的计数、守卫、失败或历史记录槽增加双线性假设。
5. 令 $E_0=\operatorname{span}\{p_1,p_2,p_3\}$。对完整实际线性菜单中的每个生成元 $U_\gamma:J\to J$，保留 $U_\gamma^*E_0\subseteq E_0$，并保留全部共同来源执行条件。计数、守卫、失败和历史槽的规则及保留责任均按 §10 的原任务定义，不并入三维方向接口。

第三通道的 (21.2)–(21.3) 必须特别具有下列精确值：

$$
C_3(h_j)=\langle e_3,v_j\rangle_K
=s^{-1}\langle c,v_j\rangle_K,\qquad
\beta_3(h_j,h_k)=\langle e_3,B(v_j,v_k)\rangle_K
=s^{-1}\langle c,B(v_j,v_k)\rangle_K. \tag{21.4}
$$

这些等式由独立校准的实际 $e_3$ 方向，或由实际 $c$ 通道及其同源尺度 $s$ 的归一化供应，保留 $c=B(b,a)$ 的符号和手性。形式系数 $\zeta_i$ 的存在及代数式 $c=B(b,a)$ 均不给任何端点的制备权限；三个实际探针及其精确等式仍是条件。

若用 §12 的有限系数证书供应预算，还完整保留定义 12.1 的取得条件：已知维数 $d$ 和独立精确校准的完整正交单位标架 $f_1,\ldots,f_d$，$K=\operatorname{span}\{f_r\}$；所有有序同源系数
$b_{kij}=\langle B(f_i,f_j),f_k\rangle_K$ 在同一版本、尺度和控制下取得。全部制备、控制、读出和共同校准的确定性误差进入 (12.1) 的 $\epsilon_{kij}$ 和 $E$；全部算术上误差或向上舍入进入 (12.2) 的 $\overline M,\overline R_A,\overline R_J$。所需共同初态、实际复位或同身份重复准备、动作次序、探针归属和读出宽度仍由来源条件供应；若操作可逆，重复控制也须保持标定不漂移。真实 $T$ 的精确完全交错性独立给定，测得的 $\widehat B$ 不要求交错。这里用 $f_r$ 区别证书的完整标架与 (21.1) 的三个带符号方向。

**定理 21.2（定理 13.2 的锐阈值版本）。** 在假设 21.1 的全部条件下，将原代数阈值 $5\alpha+\beta<1$ 替换为且仅替换为

$$
0\le\alpha<1,\qquad 0\le\beta<3(1-\alpha). \tag{21.5}
$$

则 $\dim K=3$，且

$$
s^2\in[1-\alpha,1+\alpha],\qquad s>0, \tag{21.6}
$$

$(a,b,e_3)$ 是 $K$ 的完整正交单位基。保留精确第三通道 (21.4) 后，存在唯一满射线性映射 $\Pi:J\to K$，满足定理 10.2 的全部相应结论：

$$
\Pi h_j=v_j,\qquad
C_i(x)=\langle e_i,\Pi x\rangle_K,\qquad
g_D(x,y)=\langle\Pi x,\Pi y\rangle_K,
$$

$$
\ker\Pi=\ker C=E_0^\perp=E_\infty^\perp,\qquad
\Pi D(x,y)=B(\Pi x,\Pi y). \tag{21.7}
$$

其中 $C=(C_1,C_2,C_3)$，$E_\infty$ 是所有允许有限线性操作词的回传探针的张成空间，包含空词的探针。对每个实际生成元有唯一 $A_\gamma:K\to K$，且对每个有限词 $w$ 有

$$
\Pi U_\gamma=A_\gamma\Pi,\qquad
\Pi U_w=A_w\Pi. \tag{21.8}
$$

因此距离商、联合正交商和几何商由原构造等距识别；所列同源有限操作表达式的方向读出、任务距离及二元响应因子化通过同一个 $\Pi$。阈值 (21.5) 的等号边界不能仅由这些预算纳入三维结论。

**证明。** 在 $d=2$ 时，完全交错三形式必为零；由内积非退化性 $B=0$。对正交单位对，面积预算则要求 $1\le\alpha$，与 (21.5) 矛盾。因此 $d\ne2$。若 $d\ge4$，定理 20.1 给
$\beta\ge3(1-\alpha)$，也与 (21.5) 矛盾。保留 $d\ge2$ 的原定义后，唯一剩下的是 $d=3$。对原来选定的正交单位 $a,b$，面积预算给 (21.6)；交错性给 $c\perp a,b$，故保留有符号 $e_3=c/s$ 后得到完整正交单位基。定理 20.3 的七维达到族在
$\beta=3(1-\alpha)$ 满足全部代数预算，故由这些预算单独进行维数选择时必须保留严格不等号。

为核对精确消费者，记 $S_{ij}=\langle e_i,v_j\rangle_K$。基的完整性和 (21.2) 分别给

$$
G=S^{\mathsf T}S,\qquad CF=S. \tag{21.9}
$$

若 $F\xi=0$，则 $S\xi=CF\xi=0$，从而
$\xi^{\mathsf T}G\xi=0$。因 $G\succeq0$，有 $\xi\in\ker G$。所以

$$
\Pi(F\xi)=[\xi] \tag{21.10}
$$

不依赖系数选择。$F$ 满射，且 $v_j$ 张成 $K$，故 (21.10) 定义唯一满射线性 $\Pi$。再对 $x=F\xi,y=F\eta$，

$$
C_i(x)=(S\xi)_i=\langle e_i,\Pi x\rangle_K,\qquad
g_D(x,y)=\xi^{\mathsf T}G\eta
=\langle\Pi x,\Pi y\rangle_K. \tag{21.11}
$$

三个基坐标分离 $K$，所以 $\ker\Pi=\ker C=E_0^\perp$。定义
$\iota:K\to J$，$\iota(\sum_i t_ie_i)=\sum_i t_ip_i$。
实际探针正交单位使 $\iota$ 等距；(21.11) 给 $\Pi^*e_i=p_i$，并由
$C_i(p_j)=\delta_{ij}$ 给 $\Pi p_j=e_j$。于是

$$
\Pi\iota=I_K,\qquad \iota\Pi=P_{E_0},\qquad
J=E_0\oplus\ker\Pi. \tag{21.12}
$$

商类的正交代表 $P_{E_0}x$ 的 $J$ 范数等于 $\|\Pi x\|_K$，(21.11) 则给其任务度量；这证明原有两个商到 $K$ 的等距性，度量并未另换。

若二元操作在菜单中，对 $x=F\xi,y=F\eta$，读出双线性及 (21.3) 给

$$
\begin{aligned}
C_i(D(x,y))
&=\sum_{j,k}\xi_j\eta_k\beta_i(h_j,h_k)\\
&=\left\langle e_i,B\left(\sum_j\xi_jv_j,\sum_k\eta_kv_k\right)\right\rangle_K\\
&=\langle e_i,B(\Pi x,\Pi y)\rangle_K.
\end{aligned}
$$

结合 (21.11) 及基分离性，得到 (21.7) 的二元因子化。此结论只涉及方向任务，没有改变其他记录槽。

对 $z\in E_0^\perp$ 和 $p\in E_0$，
$\langle p,U_\gamma z\rangle_J=\langle U_\gamma^*p,z\rangle_J=0$。
因此 $\ker\Pi$ 被全部实际生成元保持，
$A_\gamma(\Pi x)=\Pi U_\gamma x$ 良定义，满射性给唯一性，且可写
$A_\gamma=\Pi U_\gamma\iota$。对词长归纳，空词为恒等式，追加一生成元时用
$\Pi U_\gamma U_w=A_\gamma\Pi U_w$，便得 (21.8)。伴随不变性使每个回传探针仍在 $E_0$，空词又给反向包含，故 $E_\infty=E_0$，完成全部核等式。

同样按允许有限表达式的结构归纳，将上述线性桥和二元桥组合，便保持其 $\Pi$ 值；(21.11) 保持读出和距离。这正是原来的有限操作预测范围。任意保全部当前及未来线性读出的线性摘要 $L$ 必有 $\ker L\subseteq\ker\Pi$，所以其像满射到三维 $K$，维数至少三；$\Pi$ 达到该下界。又 $G=S^{\mathsf T}S$ 且 $v_j$ 张成三维 $K$，故 $G$ 秩三，原锚定距离的张成几何实现也至少三维。两个最小性由同一映射接合。证毕。

**推论 21.3（原有限证书的充分检验区域）。** 在假设 21.1 的全部精确消费者条件以及定义 12.1、定理 12.2 的全部证书条件下，仍取原公式

$$
\alpha_{\rm cert}=\overline R_A+(2\overline M+E)E,\qquad
\beta_{\rm cert}=\overline R_J+3(2\overline M+E)E. \tag{21.13}
$$

若

$$
0\le\alpha_{\rm cert}<1,\qquad
0\le\beta_{\rm cert}<3(1-\alpha_{\rm cert}), \tag{21.14}
$$

则定理 21.2 适用。

**证明。** 定理 12.2 在同一真实 $B$ 上，以 (21.13) 为上界预算证明原 (11.1)–(11.2)。因此可直接取
$\alpha=\alpha_{\rm cert}$、$\beta=\beta_{\rm cert}$ 代入定理 21.2，保留其余精确条件不变。

(21.13) 是保守上界，不等于真实积的最小预算。具体地，若将真实最小面积预算记为

$$
\alpha_{\rm act}(B)=
\max_{\|u\|=\|v\|=1}
\bigl|\|B(u,v)\|^2-A(u,v)\bigr|,
$$

则齐次性和零输入的直接代入说明它正是原面积分母下的最小常数，而真实最小 Jacobi 预算为 $j(B)$。证书只给
$\alpha_{\rm act}(B)\le\alpha_{\rm cert}$、$j(B)\le\beta_{\rm cert}$。
定理 20.3 的锐界和达到分类涉及 (20.1) 的实际可行预算，不声称 (21.13) 达到该锐边界。例如 §12.3 的精确七维模型已有真实最小 Jacobi 预算 $3$，同一系数绝对值和证书却给 $504$。

有限系数误差仅用于上述预算，不供应 (21.2)–(21.4) 的精确校准。完整已知标架、共同来源及制备、复位、控制条件均作为假设保留；这些条件不推出物理实现，也不从未知或不完整标架推出维数，不把带噪校准变成精确等式。有限词和有限表达式的结论不提供无限时间的预测保证。证毕。

## 22. 定量推导中经典供应者的范围

**文献范围 22.1。** Draisma–Shaw, *Some noteworthy alternating trilinear forms*,
[arXiv:1102.4768v1](https://arxiv.org/html/1102.4768v1)，定义 (2)、Theorem 2，只供应实交错三形式的奇异直线及维数排除；(19.6) 明确给出它与本题同一内积下的积非零条件的对应。该定理不要求精确面积恒等式，也不供应 (19.23) 的定量常数。

Darpö, *Vector product algebras*,
[arXiv:0810.5464v1](https://arxiv.org/html/0810.5464v1)，定义中的相容非退化对称形式、反对称乘法及精确范数恒等式是 Theorem 1 的前提。它供应精确向量积分类，适用于这里 $\alpha=0$ 的相应边界，不能直接用于一般 $\alpha>0$。定理 19.2 的等号结构通过极小三平面、定向符号及 $\rho=0$ 导出，不以该精确分类作为任意积的前提。

Baez, *The Octonions*, [§4.1](https://math.ucr.edu/home/baez/octonions/node14.html)，供应经典虚八元数叉积、半交换子归一化、范数恒等式和交错三形式的背景。式 (19.2)、(19.26)–(19.27) 在同一四元数约定中给出所需全输入恒等式和达到三元组；经典模型及其标量缩放不另作独立的新分类定理。

Bryant, *Some remarks on $G_2$-structures*,
[arXiv:math/0305124v5](https://arxiv.org/html/math/0305124v5)，§2.6，式 (2.18)，在标准 $G_2$ 形式 $\phi$ 的度量和星算子下定义
$\mathsf j_\phi(\gamma)(v,w)=*_\phi((\iota_v\phi)\wedge(\iota_w\phi)\wedge\gamma)$，并有 $\mathsf j_\phi(\phi)=6g_\phi$。它是收缩—楔积构造的背景；(19.14)–(19.20) 对任意本题资料使用给定欧氏体积，直接证明非零性和两处符号，不假设该资料的给定内积等于某个诱导 $G_2$ 度量。

这些供应者各有上述限定；任意积的定量估计与等号刚性由定理 19.2 的完整推导承担。原下确界由定理 20.1 的全类下界及定理 20.3 的全域达到者共同给出，定理 21.2 仅在假设 21.1 的全部精确共同实现条件下消费该估计。

## 追加锚（本行以下为增补区）

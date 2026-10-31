# AURIC：原生三设置的锐利稳定性

# 未来闭合与递归误差能量

**定义、定理与纸面证明　v39.0**

2026 年 10 月 31 日　Asia/Singapore

<!-- editorial-start:metadata -->
> **转写元数据（编者说明）**  
> PDF 标题：AURIC：原生三设置的锐利稳定性与未来闭合。  
> PDF 作者：AURIC research continuation。  
> PDF 主题：Sharp native three-setting stability, finite predictive closure and recursive error energy。  
> 原页眉：AURIC：原生三设置的锐利稳定性与未来闭合；v39 / 2026-10-31。原页脚为页码。  
> 源稿 SHA-256：<code>52cdb293<wbr>3a0c988a<wbr>ce04acda<wbr>cfa36cd5<wbr>1c9ab513<wbr>07017f0a<wbr>29440f8e<wbr>3e018360</code>。  
> 下文保留作者原稿，节、子节与各类陈述共用的节内计数显式展开；无编号展示式不另加编号。正文中的“本轮”、取得与复用数量、全树文件数、差异数、提交时间、来源读取和旧稿转换身份均属原作者写作时的历史陈述，不是本次转写重新完成的全树审计或内核认证。v37 本地 TeX 摘要不一致仍是原稿所述的未决历史问题，本次未重新取样或判定其原因。关于 v38 的比较沿用原作者归属及所列比较提交，未在本次确定并读取一个对应的固定 v38 稿本，故该比较未另行核验；本稿的具体推导以前文合同及已列固定供应为前提，不以待交付的 v38 文稿补足证明。
<!-- editorial-end:metadata -->

## 摘要
本稿承接 v38 的未知记录质量合同，将粗略的秩条件数界精确化。
两个设置的残差只落在两个后继差算符张成的平面；
其 Gram 矩阵给最优局部线性误差常数，每个权重可由一个消去另一权重的投影见证取得。
构造严格满足概率区间的输入族，证明两设置的全输入最坏放大率确为
$1/\kappa$，其中 $\kappa$ 是输入 Gram 矩阵的最小特征值。
随后只增加已有记录地址的两次调用设置 $B^2$：
三个记录轴线性独立，在另供第三设置完整统计合同后，
统一放大率降为 $1/\sqrt{\kappa}$，该阶也不可改进。
有共同 Lipschitz 连续模与可取得邻域时，
秩一边界的稳定率因而由原充分界的 $\epsilon^{1/3}$ 改进为
$\sqrt{\epsilon}$；给出所列合同内相同指数的下界。
另一主线将项目已有未来效果闭包落实为离散原生菜单的有限深度、最小线性均值维数
及 Gram 稳定证书。闭合可见空间上的酉更新在其固有度量下为等距，
并不自动耗散误差。结合新增 Datko 模块，给出三轴逻辑误差的离散
Lyapunov 能量判据、受迫误差级数与非酉局部过程的具体例子。
全部准备、条件后继、归一化、输入域、档案和误差来源均保留；
不运行数值数学、CAS、Lean 或门字搜索。

<a id="section-1"></a>

## 1　固定来源及本轮的增量边界

本轮固定提交为
<code>18ab1784<wbr>72d8c29e<wbr>b90d5e5f<wbr>4e6c8b4c<wbr>89038e84</code>，

提交时间为 2026-10-31 05:56:10（新加坡）。
比较基线是 v38 的
<code>621108f1<wbr>7bf2a141<wbr>b2605dda<wbr>d479f28e<wbr>d6ac4bbd</code>。

完整 theory 与 D5 子树未截断，分别有 1083 与 11660 个文件；
相关差异为七个理论文件和五个新增 D5 文件。来源检查不等于数学核验。
[[1](#bib-head)]

本轮承重来源有以下变化与延续。

1. 续卷 II 完全未改，最新末尾仍为 §§126–131。
   §105、§111 已给 $K_9J_{\rm src}=J_{\rm src}(I\otimes B)$，
   所以 $B^2$ 已由两个正向原生调用供应。
   但 §128 的任意实际输入最低统计合同只覆盖 $I,B$；
   把同输入隔离及完整后继扩展到 $B^2$ 是本稿明确增加的前件。
   [[2](#bib-continuation)]
2. 新增 v37 入库文件自述为先前作者稿转换，不是独立的新 Lean 核验。
   其页首所列源稿摘要与当前工作区 v37 TeX 字节摘要不一致，原因未确定；
   本稿不据此认证逐字同一性，也不依赖这种同一性证明数学命题。
   [[3](#bib-v37)]
3. 新增 `DatkoStability.lean` 给实 Banach 空间强连续收缩半群的
   逐向量平方轨道可积与统一指数稳定的等价式。
   本轮完整读取其声明与证明源码，未执行 Lean。
   [[4](#bib-datko)]
4. 有根历史稿新增 §§11–14：
   在另行安装的确定 floor 读口下，未来等价胞可含无限多个原始历史，
   且有有限测试深度；可递归预测商不等于原历史恢复。
   [[5](#bib-rooted)]
5. 既有 V22 §8.4、有限序列字证书模块、受控可观测完成模块
   已有未来商与有限维闭合供应。
   后两者分别使用以恒等效果为根的仪器字、或 Hamiltonian 等待菜单。
   本稿为多个终端效果与原生离散 $K$ 字给具体消费者和稳定度量，
   不将旧控制菜单直接改名。
   [[6](#bib-v22), [7](#bib-finiteword), [8](#bib-controlled)]

继续固定唯一静态整体 $(\mathcal A,\omega)$；
系统、参考、记录及制备均为其内部角色。
前半部不预设未知记录质量服从 Born；
后半部关于线性未来效果和 CPTP 逻辑通道的结论明确消费相应校准接口。
字长和迭代指标标记组合，不供应整体外的物理时钟。

<a id="section-2"></a>

## 2　未知质量合同与后继差的精确几何

<a id="def:contract"></a>

#### 定义 2.1（同输入、完整记录合同）

实际供应同一个相干代码输入

$$
\chi=J_{\rm src}(z_0\otimes|0\rangle+z_1\otimes|1\rangle),
\qquad X=(z_0\ z_1),\qquad \operatorname{Tr}(X^*X)=1.
$$

$J_{\rm src}$ 是来源的系统–记录等距；$z_i\in\mathcal H_{13}$。
令 $G=X^*X\succ0$，并置

$$
G=\frac{I+g\cdot\sigma}{2},\qquad
\kappa=\lambda_{\min}G,\qquad d_G=\det G=\kappa(1-\kappa)>0.
$$

对实际记录设置 $S_i$，

$$
P_i=S_i^{\mathsf T}|0\rangle\langle0|\overline{S_i}
=\frac{I+n_i\cdot\sigma}{2},\qquad |n_i|=1.
$$

记

$$
s_i=g\cdot n_i,\quad
t_{i0}=\frac{1+s_i}{2},\quad t_{i1}=\frac{1-s_i}{2},
\quad p_i=t_{i0}t_{i1},\quad q_i=4p_i=1-s_i^2.
$$

实际质量 $m_{i0},m_{i1}$ 无失败、非负、无条件归一，
在系统后续程序选择前固定；
令 $z_{i\alpha}=XS_i^{\mathsf T}|\alpha\rangle$、
$\rho_{i\alpha}=|z_{i\alpha}\rangle\langle z_{i\alpha}|/t_{i\alpha}$。
正质量分支保留完整记录，后继是
$J_{\rm src}(z_{i\alpha}/\sqrt{t_{i\alpha}},\alpha)$，
并沿用同一个已重构的条件系统终端。
令

$$
\delta_i=m_{i0}-t_{i0}=-(m_{i1}-t_{i1}),
\qquad -t_{i0}\le\delta_i\le t_{i1}.
$$

输入覆盖、无失败与纯后继不是由矩阵的数学存在自动供应的。
若有失败或代码外后继，须另列无条件预算。
对 $i=0,1$ 先取 $S_0=I,S_1=B$；第三设置 $S_2=B^2$ 在第 4 节另加完整合同。

设两个归一系统后继为 $\rho_{i0},\rho_{i1}$，
定义后继差 $H_i=\rho_{i0}-\rho_{i1}$。
忽略记录的系统关系精确为

$$
A_i=XX^*+\delta_iH_i,\qquad
A_i-A_0=\delta_iH_i-\delta_0H_0.
$$

令 $Q=XG^{-1/2}$，则 $Q^*Q=I$。
在这个已知二维支持内写

$$
Q^*H_iQ=h_i\cdot\sigma.
$$

这些 $H_i$ 由实际输入与指定后继决定，不包含正在识别的未知 $\delta_i$。

<a id="thm:geometry"></a>

#### 定理 2.2（后继差的精确三维几何）

令 $a=2\sqrt{d_G}=\sqrt{1-|g|^2}$。
当 $g\ne0$ 时定义
$C_g=P_{g^\perp}+aP_g$，当 $g=0$ 时令 $C_g=I$。
则

$$
\boxed{h_i=\frac{a\,C_gn_i}{q_i}.}
$$

特别地

$$
\|h_i\|^2=\frac{d_G}{p_i},\qquad
h_i\cdot h_j=
\frac{d_G(n_i\cdot n_j-s_is_j)}{4p_ip_j}.
$$

若 $n_i,n_j$ 不平行，令
$w_{ij}=(n_i\times n_j)/|n_i\times n_j|$，
则夹角 $\vartheta_{ij}$ 满足

$$
\sin\vartheta_{ij}
=\frac{|n_i\times n_j|\sqrt{4d_G+(g\cdot w_{ij})^2}}
{\sqrt{q_iq_j}}>0.
$$

**证明。**

在输入二元空间，

$$
\frac{P_i}{t_{i0}}-\frac{I-P_i}{t_{i1}}
=\frac{2(n_i\cdot\sigma-s_iI)}{q_i}.
$$

用 $X=Q\sqrt G$ 左右共轭，即得 $Q^*H_iQ$。
将坐标临时转到 $g=|g|e_z$，有
$G=\operatorname{diag}((1+|g|)/2,(1-|g|)/2)$。
逐个矩阵元计算，垂直分量系数为 $a/q_i$，
平行分量系数为 $a^2/q_i$，得第一式。
这是证明中的坐标选择，不是新增控制操作。

因 $C_g^2=I-gg^{\mathsf T}$，

$$
|C_gn_i|^2=q_i,\qquad
(C_gn_i)\cdot(C_gn_j)=n_i\cdot n_j-s_is_j,
$$

得到范数与内积。
对叉积使用
$(Cu)\times(Cv)=\det(C)C^{-\mathsf T}(u\times v)$；
这里 $\det C_g=a$，故

$$
|(C_gn_i)\times(C_gn_j)|^2
=|n_i\times n_j|^2[\,a^2+(g\cdot w_{ij})^2\,].
$$

除以两个向量的范数即得夹角公式。

**□**

<a id="section-3"></a>

## 3　两个设置：最优常数、两项读出与锐利退化

记

$$
A=\|h_0\|^2,\qquad B_1=\|h_1\|^2,\qquad C=h_0\cdot h_1,
\qquad
\Gamma=
\begin{pmatrix}A&-C\\-C&B_1\end{pmatrix}.
$$

$\Gamma$ 是响应 Gram 矩阵，区别于输入 Gram 矩阵 $G$。
$n_0,n_1$ 不平行时，定理 [2.2](#thm:geometry) 给 $\Gamma\succ0$。

<a id="thm:optimal"></a>

#### 定理 3.1（精确残差恒等式与最优线性常数）

对 $\Delta=A_1-A_0$，

$$
\boxed{\|\Delta\|_{\mathrm{op}}^2
=(\delta_0,\delta_1)\Gamma(\delta_0,\delta_1)^{\mathsf T}.}
$$

因此若 $\|\Delta\|\le\eta$，

$$
\sqrt{\delta_0^2+\delta_1^2}\le\frac{\eta}{\sqrt{\lambda_{\min}\Gamma}},
\qquad
\lambda_{\min}\Gamma=
\frac{A+B_1-\sqrt{(A-B_1)^2+4C^2}}2.
$$

最优单坐标常数为

$$
\boxed{
|\delta_0|\le C_0\eta,\quad
C_0=\frac1{\|h_0\|\sin\vartheta_{01}},\qquad
|\delta_1|\le C_1\eta,\quad
C_1=\frac1{\|h_1\|\sin\vartheta_{01}}.
}
$$

这些是固定 $X,S_0,S_1$ 下的最优齐次常数，
并可在任意小残差、概率严格合法的邻域内达到。

**证明。**

$Q^*\Delta Q=(\delta_1h_1-\delta_0h_0)\cdot\sigma$，
其算子范数为对应实向量长度，得恒等式与特征值界。
固定 $\delta_0$，对自由 $\delta_1$ 作正交投影最小化，
最小残差为 $|\delta_0|\|h_0\|\sin\vartheta_{01}$，
在 $\delta_1=(C/B_1)\delta_0$ 达到。
另一个坐标同理。
联合常数沿 $\Gamma$ 的最小特征向量达到。
由于全部 $t_{ij}>0$，把这些方向乘充分小的标量后，
所有 $m_{ij}$ 都在 $(0,1)$ 内，故锐利性保留概率可行性。
对于给定的大残差还应与质量区间相交，不宣称同一方向能越过概率端点。

**□**

<a id="section-3-1"></a>

### 3.1　每个未知权重只需一个消干扰投影

<a id="cor:witness"></a>

#### 推论 3.2（两项专门见证）

令

$$
e_0=
\frac{h_0-(C/B_1)h_1}{\sqrt{A-C^2/B_1}},
\qquad
F_0=Q\frac{I+e_0\cdot\sigma}{2}Q^*.
$$

则

$$
\boxed{\operatorname{Tr}(F_0\Delta)=-\delta_0/C_0.}
$$

交换 $0,1$ 可构造 $F_1$，满足 $\operatorname{Tr}(F_1\Delta)=\delta_1/C_1$。
因此两项系统事件即可分别识别两个未知权重偏差。

**证明。**

$e_0$ 与 $h_1$ 正交，
$\operatorname{Tr}[(I+e_0\cdot\sigma)(\delta_1h_1-\delta_0h_0)\cdot\sigma/2] =-\delta_0\sqrt{A-C^2/B_1}$。
后者为 $-\delta_0/C_0$。

**□**

原十三维七地址射影密度可将每个 $F_i$ 任意逼近为
$K_f^*E_wK_f$；目标投影只是编译目标，不是另授的自由测量。
若门字逼近误差至多 $\tau_i$，实际事件概率差的可靠上界为 $r_i$，
则效果误差至多 $2\tau_i$，
结合 $\|\Delta\|_1\le2$ 得

$$
|\delta_i|\le C_i(r_i+4\tau_i).
$$

这里两项见证属于不同后续程序；记录质量必须在后续选择前固定。
有限频率须另有置信控制。若后继、支持或总质量改变，
残差不再限于这个二维平面，不能继续免费使用两项见证。

<a id="section-3-2"></a>

### 3.2　黄金两设置的精确条件数

沿用

$$
x=\varphi^{-1},\quad y=\sqrt x,\quad \zeta=e^{3\pi i/5},
\qquad
B=
\begin{pmatrix}-x&y\zeta^{-1}\\y\zeta^{-1}&-x\zeta^3\end{pmatrix}.
$$

对 $S_0=I,S_1=B$，

$$
\beta=xy=x^{3/2},\qquad |n_0\times n_1|=2\beta.
$$

令 $w=(n_0\times n_1)/(2\beta)$、
$s=\sqrt{4d_G+(g\cdot w)^2}$，则

$$
\boxed{
C_0=\frac{2p_0\sqrt{p_1}}{\beta\sqrt{d_G}\,s},
\qquad
C_1=\frac{2p_1\sqrt{p_0}}{\beta\sqrt{d_G}\,s}.
}
$$

若输入靠近秩一而 $|g\cdot w|$ 保持正下界，这个公式给
$O(d_G^{-1/2})$ 的上界；
若 $g$ 落在两个记录轴的平面中，并且 $p_0,p_1$ 不趋零，
则放大率为 $O(d_G^{-1})$。
因此退化还取决于关系方向，单个 $\kappa$ 是全输入的保守参数。

<a id="thm:twosharp"></a>

#### 定理 3.3（两设置的 $1/\kappa$ 最坏阶确实锐利）

置

$$
n=\frac{n_0+n_1}{2x},\qquad
G_\kappa=\frac{I+(1-2\kappa)n\cdot\sigma}{2},
\qquad 0<\kappa\le\frac12.
$$

任取系统二维等距 $Q$，取 $X=Q\sqrt{G_\kappa}$。
对固定 $0<\delta\le x^2/2$，指定
$\delta_0=\delta,\delta_1=-\delta$，则全部质量合法，而且

$$
\boxed{
\|A_1-A_0\|_{\mathrm{op}}
=\frac{8\delta\,\kappa(1-\kappa)}
       {1+4x\kappa(1-\kappa)}.
}
$$

当 $\kappa\downarrow0$，残差与 $\kappa$ 同阶，而质量偏差固定。

**证明。**

黄金恒等式给 $n_0\cdot n_1=-x^3$、
$1-x^3=2x^2$，故 $n$ 为单位向量，且 $n\cdot n_i=x$。
记 $d_G=\kappa(1-\kappa)$，则

$$
q_0=q_1=x(1+4xd_G),\qquad
p_0=p_1=\frac{x(1+4xd_G)}4.
$$

又 $t_{i1}=[1-(1-2\kappa)x]/2\ge(1-x)/2=x^2/2$，
所以所给正负偏差合法。
$n_0+n_1=2xn$ 是 $C_g$ 的平行方向，
因此

$$
h_0+h_1=\frac{8d_G}{1+4xd_G}\,n.
$$

残差为 $-\delta(h_0+h_1)\cdot\sigma$，得结论。
此族的响应 Gram 最小特征值为
$32d_G^2/(1+4xd_G)^2$；
$(\delta,-\delta)$ 正是最弱方向，因而同时达到联合范数界。

**□**

v38 的 $1/\kappa$ 上界常数不是这里的最优常数，
但其全输入最坏阶现在已有严格下界。
这个未知质量族只满足所列合同，不宣称保留旧反模型的所有校准条款。

<a id="section-4"></a>

## 4　增加第三原生设置：统一改善到平方根阶

<a id="statement-4-1"></a>

#### 定义 4.1（三设置的新增统计前件）

在同一个实际输入上，令

$$
S_0=I,\qquad S_1=B,\qquad S_2=B^2.
$$

三个设置全部满足定义 [2.1](#def:contract)，
特别是第三设置也有无失败质量、指定细分支后继、同一条件终端和先于后续的因果固定。
其系统隔离预算为

$$
\|A_j-A_0\|_{\mathrm{op}}\le\eta_j,\qquad j=1,2.
$$

源中的设置编号为 $I,B^2,B$；这里只按幂次重新编号。
由整个二十六维代码上的 $K_9J_{\rm src}=J_{\rm src}(I\otimes B)$，
$B^2$ 是两个精确正向调用。
源码已有这个门字，却不自动供应定义中的任意输入第三设置统计量词。
[[2](#bib-continuation)]

<a id="lem:axes"></a>

#### 引理 4.2（三个原生记录轴线性独立）

$n_0,n_1,n_2$ 线性独立。
因此

$$
M_0=\sum_{j=1}^2(n_0\times n_j)(n_0\times n_j)^{\mathsf T}
$$

在 $n_0^\perp$ 上正定。记其最小特征值为 $c_0>0$；
$c_0$ 仅依赖固定黄金块，与输入 $X$ 无关。

**证明。**

$B=\zeta[I+(\zeta-1)Q_R]$，
$Q_R=|(y,x)\rangle\langle(y,x)|$。
其 Bloch 旋转轴为

$$
q_R=(2xy,0,x-x^2),
$$

旋转角为 $\theta=\pm3\pi/5$。
$B$ 对称，故本稿 $B^{\mathsf T}$ 轴约定正是同一个旋转轨道。
若 $a_R=n_0\cdot q_R=x-x^2=x^3$，
将旋转轴临时取为第三轴，可直接展开行列式：

$$
|\det(n_0,n_1,n_2)|
=
|2a_R(1-a_R^2)\sin\theta(1-\cos\theta)|>0.
$$

于是两个叉积张成 $n_0^\perp$，得正定性。

**□**

这里还可给完全代数的保守常数。
记 $u=n_0\cdot n_1=-x^3$、
$v=n_0\cdot n_2=2x^4-1$，
则 $n_1\cdot n_2=u$。
两个叉积的 Gram 矩阵的迹与行列式分别为

$$
T_0=4x^3+4x^4(1-x^4),\qquad
D_0=4x^5(1-x^4).
$$

因此

$$
\boxed{
c_0\ge\underline c_0:=\frac{D_0}{T_0}
=\frac{x^2(1-x^4)}{1+x(1-x^4)}>0.
}
$$

这些恒等式只用 $x^2+x=1$；
本稿未对常数作数值计算。

<a id="thm:three"></a>

#### 定理 4.3（三设置统一稳定界）

在三设置完整合同下，

$$
\boxed{
|\delta_0|
\le
\frac{\sqrt{q_0}}{2\sqrt{d_Gc_0}}
\sqrt{q_1\eta_1^2+q_2\eta_2^2}
\le
\frac{\sqrt{\eta_1^2+\eta_2^2}}{2\sqrt{d_Gc_0}}.
}
$$

故全输入最坏放大率为 $O(\kappa^{-1/2})$。
重选基准设置并使用相应两条隔离边，可同样控制其余质量。

**证明。**

将 $\delta_jh_j-\delta_0h_0$ 投影到 $h_j^\perp$，
得到

$$
\eta_j^2\ge
\delta_0^2\|h_0\|^2\sin^2\vartheta_{0j}
=
\delta_0^2
\frac{a^2|n_0\times n_j|^2
[\,a^2+(g\cdot w_{0j})^2\,]}{q_0^2q_j}.
$$

乘 $q_j$ 再对 $j=1,2$ 求和：

$$
\sum_jq_j\eta_j^2
\ge
\delta_0^2\frac{a^2}{q_0^2}
\left(a^2\operatorname{Tr} M_0+g^{\mathsf T}M_0g\right).
$$

因为 $M_0\succeq c_0P_{n_0^\perp}$ 且 $\operatorname{Tr} M_0\ge c_0$，

$$
a^2\operatorname{Tr} M_0+g^{\mathsf T}M_0g
\ge c_0\left(a^2+|P_{n_0^\perp}g|^2\right)
=c_0q_0.
$$

代入 $a=2\sqrt{d_G}$，得到第一界；$q_i\le1$ 给第二界。
最后 $d_G=\kappa(1-\kappa)\ge\kappa/2$。

**□**

改进来自三个记录轴消除了两轴共平面时最坏的补偿方向；
没有删除秩退化，也没有从酉性单独推出统计隔离。

<a id="cor:threewitness"></a>

#### 推论 4.4（第三设置仍只需两项消干扰见证）

对 $j=1,2$，令 $e_{0|j}$ 为 $h_0$ 在 $h_j^\perp$
上的投影单位方向，取

$$
F_{0|j}=Q\frac{I+e_{0|j}\cdot\sigma}{2}Q^*.
$$

则

$$
z_j:=\operatorname{Tr}[F_{0|j}(A_j-A_0)]
=-\delta_0\|h_0\|\sin\vartheta_{0j}.
$$

若两个原生近似事件给 $|z_j|\le R_j=r_j+4\tau_j$，
定理 [4.3](#thm:three) 中可直接将 $\eta_j$ 替换成 $R_j$：

$$
\boxed{
|\delta_0|
\le
\frac{\sqrt{R_1^2+R_2^2}}{2\sqrt{d_Gc_0}}.
}
$$

**证明。**

每项见证消去 $\delta_j$，给出的正是主定理证明所需的
$|\delta_0|\|h_0\|\sin\vartheta_{0j}$ 上界。
不需要先重建两个完整差算符。

**□**

该两项结论只针对一个指定基准质量及两条比较边；
控制全部三个设置可重选基准并计入相应事件。
后续见证字的存在来自原七地址射影密度，字长及实际准备次数并未免费给出。

<a id="thm:threesharp"></a>

#### 定理 4.5（三设置平方根阶不可改善）

在三设置合同内，不存在全输入的
$O(\kappa^{-\alpha})$ 线性稳定常数，其中 $\alpha<1/2$。

**证明。**

取 $\psi\perp\psi'$、$r=(|0\rangle+|1\rangle)/\sqrt2$、
$r'=(|0\rangle-|1\rangle)/\sqrt2$，供应

$$
\chi_\tau=
J_{\rm src}
\left(\sqrt{1-\tau^2}\,\psi\otimes r+
\tau\psi'\otimes r'\right),
\qquad0<\tau\le1/\sqrt2.
$$

则 $t_{00}=t_{01}=1/2$、
$\kappa=\tau^2$、$d_G=\tau^2(1-\tau^2)$。
指定 $m_0=(1,0)$，另两设置取 $m_j=t_j$。
于是 $\delta_0=1/2$，且

$$
\eta_1=\eta_2=\sqrt{d_G}.
$$

残差向量长度为 $\sqrt{2d_G}$，而目标偏差固定。
若放大率为 $O(\kappa^{-\alpha})$、$\alpha<1/2$，
其预测上界趋于零，矛盾。

**□**

<a id="section-5"></a>

## 5　跨秩一边界：平方根误差率及其最坏下界

<a id="thm:bridge"></a>

#### 定理 5.1（可取得邻域的三设置连续桥）

设目标为 $\chi_0=J_{\rm src}(\psi\otimes r)$。
实际供应

$$
\chi_\tau=J_{\rm src}
\left(\sqrt{1-\tau^2}\,\psi\otimes r+\tau\psi'\otimes r'\right),
\quad 0<\tau\le1/\sqrt2,
$$

其中系统与记录两组向量分别正交归一。
每个 $\tau$ 的三个设置满足完整合同、共用同一条件终端，
且聚合隔离预算为

$$
E_\tau=\sqrt{\eta_{1,\tau}^2+\eta_{2,\tau}^2}\le\epsilon.
$$

同一实际基准记录规则满足
$|m_{00}(\chi_\tau)-m_{00}(\chi_0)|\le\omega(\tau)$。
则

$$
\boxed{
|m_{00}(\chi_0)-t_{00}(\chi_0)|
\le
\omega(\tau)+\tau^2+
\frac{\epsilon}{2\sqrt{c_0}\,\tau\sqrt{1-\tau^2}}.
}
$$

若 $\omega(\tau)\le L\tau$、$0<\epsilon\le1/2$，
取 $\tau=\sqrt\epsilon$，得到

$$
\boxed{
|m_{00}(\chi_0)-t_{00}(\chi_0)|
\le
\left(L+\frac1{\sqrt{2c_0}}\right)\sqrt\epsilon+\epsilon.
}
$$

**证明。**

该 Schmidt 形式给 $\kappa_\tau=\tau^2$、
$d_G=\tau^2(1-\tau^2)$，
纯联合态迹距离为 $\tau$，指定记录投影的平方质量变化至多 $\tau^2$。
对满秩输入用定理 [4.3](#thm:three)，再沿
$m_{00}(\chi_0)$、$m_{00}(\chi_\tau)$、
$t_{00}(\chi_\tau)$、$t_{00}(\chi_0)$ 作三角估计。
最后 $\sqrt{1-\tau^2}\ge1/\sqrt2$，代入所选 $\tau$。

**□**

与 v38 的 $\epsilon^{1/3}$ 充分率相比，
该改进额外消费第三设置及统一邻域隔离。
若 $\epsilon=0$ 且 $\omega(\tau)\to0$，令 $\tau\downarrow0$
即得精确秩一延拓。终端连续性仍不能替代记录连续性。
[[2](#bib-continuation)]

<a id="thm:bridgesharp"></a>

#### 定理 5.2（固定正 Lipschitz 模下平方根指数最优）

固定 $L>0$。在上述实际输入曲线与未知记录规则的合同类中，
不存在一般为 $o(\sqrt\epsilon)$ 的秩一目标误差界。

**证明。**

采用定理 [4.5](#thm:threesharp) 的平衡曲线，
故 $t_{00}(\tau)\equiv1/2$。
固定 $0<b\le1/2$，指定

$$
\delta_0(\tau)=(b-L\tau)_+,\qquad
\delta_1(\tau)=\delta_2(\tau)=0,
\qquad \delta_0(0)=b.
$$

所有质量合法且归一，正质量分支采用既定后继。
同一基准规则满足

$$
|m_{00}(\chi_\tau)-m_{00}(\chi_0)|
=b-(b-L\tau)_+\le L\tau.
$$

此曲线有 $\|H_0\|=2\tau\sqrt{1-\tau^2}$，所以

$$
E_\tau
=2\sqrt2\,\tau\sqrt{1-\tau^2}(b-L\tau)_+
\le\frac{b^2}{\sqrt2L},
$$

其中使用
$\tau(b-L\tau)_+\le b^2/(4L)$。
给定足够小的 $\epsilon$，
取 $b=\sqrt{\sqrt2L\,\epsilon}$。
当 $\epsilon\le1/(4\sqrt2L)$ 时 $b\le1/2$，且全部曲线输入都满足
$E_\tau\le\epsilon$；
目标偏差却为

$$
|m_{00}(\chi_0)-t_{00}(\chi_0)|
=\sqrt{\sqrt2L}\,\sqrt\epsilon.
$$

因此不存在所述统一更小阶。

**□**

下界比较的是具有同一个 $L>0$ 的一族未知记录规则；
不声称它们是 Born/Lüders 仪器，也不声称延续旧校准族的所有全域条款。
其输入域就是所列曲线及对应设置。
定理给指数锐利性，未声称上界常数最优。

<a id="section-6"></a>

## 6　有限未来闭合：离散原生菜单的具体证书

本节声明线性终端接口 $p_s(\rho)=\operatorname{Tr}(\rho E_s)$，
固定有限载体 $\mathcal H_D$、处处合法的原生酉菜单 $\{K_j\}$ 与完整终端 POVM
$\{E_s\}$。未来只查询这些终端及允许后续；
原程序档案继续保留，但本节的有限维未来域不包含字面档案查询。
这不是用 Born 消费者反向证明前几节未知记录质量。

<a id="statement-6-1"></a>

#### 定义 6.1（多终端未来效果升链）

$$
V_0=\operatorname{span}_{\mathbb R}\{I,E_s\},\qquad
V_{n+1}=V_n+\sum_jK_j^*V_nK_j,\qquad
V_\infty=\bigcup_nV_n.
$$

原生字 $w=j_1\cdots j_\ell$ 按调用顺序书写，
$K_w=K_{j_\ell}\cdots K_{j_1}$。

<a id="thm:closure"></a>

#### 定理 6.2（精确有限截断）

$V_n$ 恰为长度至多 $n$ 的全部未来效果连同 $I$ 的实张成。
若某一步 $V_{n+1}=V_n$，则以后永久相等。
因此存在

$$
\boxed{L\le D^2-\dim V_0}
$$

使 $V_L=V_\infty$；更细地 $L\le\dim V_\infty-\dim V_0$。
V22 的全部未来等价可以由这一个有限字长截断完整刻画。

**证明。**

长度表示由归纳得到，外侧增加 $K_j^*(\cdot)K_j$ 对应先调用 $j$。
若相邻相等，每个生成元均把这个空间映入自身，重复递推不会新增方向。
稳定前每步维数至少增长一，而
$\dim_{\mathbb R}\operatorname{Herm}(\mathcal H_D)=D^2$，
故给出界。V22 的未来商由对全部 $V_\infty$ 的迹配对相等定义，
代入 $V_\infty=V_L$ 即得有限截断。

**□**

这是标准有限维升链论证在当前多个终端、离散字菜单中的应用。
有限序列字证书模块有以 $I$ 为根的仪器字供应；
若直接把它所有生成器改成酉共轭，根 $I$ 永远不增长。
受控可观测完成模块则使用 Hamiltonian 等待及交换子闭包。
两者支持相同线性代数原则，但不替代这里的具体原生接口。
[[7](#bib-finiteword), [8](#bib-controlled), [6](#bib-v22)]

<a id="thm:fullspace"></a>

#### 定理 6.3（射影密度与完整未知态的最小线性读数）

若 $D\ge2$，原生字在 $PU(D)$ 稠密，且一个终端效果非标量，
则

$$
V_\infty=\operatorname{Herm}(\mathcal H_D).
$$

若一族固定 Hermitian 读口的实线性均值
$q_a(\rho)=\operatorname{Tr}(\rho F_a)$ 要对全部密度矩阵预测全部该未来，
其充要条件为

$$
V_\infty\subseteq\operatorname{span}_{\mathbb R}\{I,F_a\}.
$$

因此在射影稠密情形，至少需要 $D^2-1$ 个独立归一态均值。

**证明。**

有限维的 $V_\infty$ 闭，故由原生射影密度包含非标量效果 $E$ 的整个酉共轭轨道。
对角化 $E$ 并交换两个不同特征值，差给出一个
$|i\rangle\langle i|-|j\rangle\langle j|$ 方向。
继续作数学酉共轭，得到全部无迹对角方向及实、虚非对角方向。
加上 $I$ 即为整个 Hermitian 空间。
这一步证明张成，不授予任意连续酉的实际调用。

读数张成包含条件显然充分。
若不包含，可取无迹 Hermitian $H$，
使它与全部当前 $F_a$ 正交，却不与某个未来效果正交。
充分小的 $\rho_\pm=I/D\pm tH$ 都是密度矩阵；
它们当前均值相同而未来不同，证明必要性及维数界。

**□**

这个最小维数结论针对全密度矩阵域的固定线性读出，
不禁止不连续的集合论编码，也不免费扩充实际准备域。
已知的固定 qubit 码上仍可用三轴恢复逻辑态。
若门把态带离该码，三轴作为当前自治摘要则须重新证明，
或保留当前编码与程序关系。

对当前 $\mathcal H_{13}$ 的完整计算终端，非零投影有十三个，
故 $\dim V_0=13$，取 $L\le169-13=156$。
若只选五前缀读口，$\dim V_0=5$，取 $L\le164$。
$\mathcal H_{89}$ 的旧十位终端看到八位合法内前缀；
无相邻 $11$ 的前缀数满足 Fibonacci 递推，为 $F_{10}=55$。
其中末位零的 $34$ 个投影各秩二，末位一的 $21$ 个各秩一，
总秩 $2\cdot34+21=89$。
所以旧终端仍只有 $55$ 个非零效果，取

$$
L\le89^2-55=7866.
$$

这些是纸面维数上界，不是最短门字、样本数或取得成本结论。
完整未来线性态参数数目分别为 $168$ 与 $7920$，
并不把原生可达纯态域自动扩充为实际可准备的全部混态。

<a id="section-6-1"></a>

### 6.1　完整未来闭合后的酉等距

<a id="thm:isometry"></a>

#### 定理 6.4（可见关系的固有度量保持）

令 $V=V_\infty$，以 Hilbert–Schmidt 内积定义投影 $P_V$。
则

$$
K_j^*VK_j=V,\qquad
P_V(K_jHK_j^*)=K_jP_V(H)K_j^*.
$$

故对任意原生字与两个态，

$$
\boxed{
\|P_V(K_w(\rho-\sigma)K_w^*)\|_{\rm HS}
=\|P_V(\rho-\sigma)\|_{\rm HS}.
}
$$

在 $V$ 的无迹部分选 Hilbert–Schmidt 正交归一基，
所得均值坐标按实正交矩阵更新。

**证明。**

闭合先给包含；有限维酉共轭为单射，左右同维，故必相等。
它保持 HS 内积，因而也保持 $V^\perp$，故与投影对易。
余下结论由酉共轭等距得到。

**□**

因此可递归观察商能去掉永久不可见的关系，
但在可逆菜单下不会继续压缩已经保留的区别。
$V$ 未必对矩阵乘法闭合，不能据此自动称它为一个新的量子子系统；
$P_V(\rho)$ 只是可见关系坐标，未声称它总是密度矩阵。

<a id="section-7"></a>

## 7　有限未来见证的 Gram 稳定性

令 $r=\dim V_\infty-1>0$。
从长度不超过 $L$ 的实际字效果中选取 $r$ 个
$A_\ell=K_{w_\ell}^*E_{s_\ell}K_{w_\ell}$，
使

$$
B_\ell=A_\ell-\frac{\operatorname{Tr} A_\ell}{D}I
$$

构成 $V$ 无迹部分的一组基。
定义

$$
\mathsf G_{\ell m}=\operatorname{Tr}(B_\ell B_m),\qquad
\alpha=\lambda_{\min}\mathsf G>0,\qquad
x_\ell(\rho)=\operatorname{Tr}(\rho A_\ell)-\frac{\operatorname{Tr} A_\ell}{D}.
$$

$\mathsf G$ 是未来见证的 Gram 矩阵，
不同于输入 $G$ 和两设置响应 $\Gamma$。

<a id="thm:frame"></a>

#### 定理 7.1（精确关系度量与全部未来误差）

对 $\delta x=x(\rho)-x(\sigma)$，

$$
\boxed{
\|P_V(\rho-\sigma)\|_{\rm HS}^2
=\delta x^{\mathsf T}\mathsf G^{-1}\delta x
\le\frac{\|\delta x\|_2^2}{\alpha}.
}
$$

若 $\{E_s\}$ 为完整 POVM，则对任意长度的精确未来字 $w$，

$$
\boxed{
\operatorname{TV}(p_w(\rho),p_w(\sigma))
\le
\frac12\|P_V(\rho-\sigma)\|_1
\le
\frac{\sqrt D}{2\sqrt\alpha}\|\delta x\|_2.
}
$$

常数不随未来字长增加，也不乘原终端标签数。

**证明。**

$P_V(\rho-\sigma)$ 无迹，写成 $\sum_\ell c_\ell B_\ell$。
与各 $B_m$ 配对，得 $\delta x=\mathsf Gc$；
其 HS 范数平方为
$c^{\mathsf T}\mathsf Gc=\delta x^{\mathsf T}\mathsf G^{-1}\delta x$。
谱界给后一不等式。

任意未来终端并事件的效果属于 $V$，故与 $\rho-\sigma$ 的配对
等于与其投影的配对。
该投影无迹，而并事件效果位于 $[0,I]$，
故绝对配对至多半迹范数。
总变差等于并事件差的最大值，再用
$\|H\|_1\le\sqrt D\|H\|_{\rm HS}$ 即得。

**□**

在同一基中，原生更新写为 $x'=R_jx$。
定理 [6.4](#thm:isometry) 等价于

$$
\boxed{R_j^{\mathsf T}\mathsf G^{-1}R_j=\mathsf G^{-1}.}
$$

所以一般非正交读数下的稳定标尺是 Gram 逆度量；
它不要求读数更新矩阵在普通欧氏坐标下逐项为酉或正交。

<a id="statement-7-2"></a>

#### 推论 7.2（带噪均值的合法修复）

合法均值体
$\mathcal X=\{x(\rho):\rho\succeq0,\operatorname{Tr}\rho=1\}$ 紧且凸。
若原始表距真实表的欧氏误差至多 $\epsilon$，
投影到 $\mathcal X$ 后该欧氏预算不增，
于是全部未来终端 TV 至多
$\sqrt D\,\epsilon/(2\sqrt\alpha)$。

**证明。**

线性映射将紧凸密度矩阵集送为紧凸集。
欧氏正交投影不会增加到任何合法集合点的距离。
选取投影表的任意合法完成，应用定理 [7.1](#thm:frame)。

**□**

这里不增的是表的欧氏误差；
不能把它直接说成 Gram 度量投影不增。
若 $V$ 不是全矩阵空间，不同合法完成可能存在，但它们属于同一未来等价类。
实际未来控制的误差仍须另计：
若字长为 $\ell$、逐调用算子误差为 $\epsilon_t$、
终端效果误差为 $\gamma_s$，则保守效果预算为

$$
\|\widetilde A_{w,s}-A_{w,s}\|_{\mathrm{op}}
\le\gamma_s+2\sum_{t=1}^{\ell}\epsilon_t.
$$

<a id="section-7-1"></a>

<!-- editorial-start:control -->
> **局部适用条件（编者说明）** 上一无编号控制误差界采用同一有限载体上的精确酉调用 $K_t$，并要求实际近似调用 $\widetilde K_t$ 也是该载体上的酉算符，或至少是算子范数不超过一的收缩，满足 $\|\widetilde K_t-K_t\|_{\mathrm{op}}\le\epsilon_t$；精确终端为效果 $0\le E_s\le I$，且 $\|\widetilde E_s-E_s\|_{\mathrm{op}}\le\gamma_s$。在这些条件下，乘积望远镜界与两侧共轭给出原文的 $\gamma_s+2\sum_t\epsilon_t$。任意放大的近似算符、泄漏到未列载体或失败后的条件归一化不由这个预算覆盖，须另列合同与误差；数学酉近似的存在不等于实际调用已满足条件。
<!-- editorial-end:control -->

### 7.1　闭合深度与统计条件数相互独立

取一般数学菜单 $K=R_y(\theta)$、终端 $E=(I+Z)/2$，
$0<\theta<\pi$。
则

$$
V_0=\operatorname{span}\{I,Z\},\qquad
V_1=\operatorname{span}\{I,Z,X\}=V_\infty.
$$

深度恒为一。
但对 $B_0=Z/2$、$B_1=K^*ZK/2$，

$$
\mathsf G=\frac12
\begin{pmatrix}1&\cos\theta\\\cos\theta&1\end{pmatrix},
\qquad
\alpha=\frac{1-|\cos\theta|}{2}\to0.
$$

所以有限闭合不供应良好条件数。
取 $\theta=\pi/(2N)$，两个 $X$ 本征态的当前 $Z$ 概率相同，
一步后的概率差为 $|\sin\theta|$，
而 $N$ 步后差为一。
精确的新方向即使很小，也不能按“近似不增长”永久删除。
这是一般菜单族的反例，不授予项目自由可调的 $\theta$。

<a id="section-7-2"></a>

### 7.2　原生反例、实际取得与档案边界

在当前唯一种子 $v=e_{00100}$ 上，
令 $u=e_{00000}$。
$K_3$ 保持 $\operatorname{span}\{u,v\}$，其限制正是黄金活动块，
两个正原生历史

$$
\psi_+=K_3v,\qquad
\psi_-=K_3^9v=K_3^*v
$$

当前全部计算终端概率相同，
仅 $p_u=x,p_v=x^2$ 非零。
共同再调用一次 $K_3$，却有

$$
|\langle v|K_3\psi_+\rangle|^2=x^4,\qquad
|\langle v|K_3\psi_-\rangle|^2=1.
$$

这是 V22 黄金反例在当前唯一种子与地址上的消费者。
[[6](#bib-v22), [2](#bib-continuation)]
按 v37 五前缀轴的位次 $(b_1,b_3,b_2)$，
二者当前均值同为 $(0,x^2,0)$，下一步第二轴不同。
该反例在完整载体中，不在 v37 的固定信息完备 qubit 码内。

若初始准备域不受后续保持，不能先压缩各 $V_n$ 再用相邻相等判定永久闭合：
四维循环移位、终端 $|3\rangle\langle3|$、
初始候选 $|0\rangle,|1\rangle$，
在零步和一步均给零，二步却被区分。
必须在完整载体或真正后继封闭的域上递推。

多个可能测试的语义存在，也不等于在不可复制、不可复位的单个来源上
已实际取得全部测试。
新增 rooted 稿在其确定 floor 读口合同中给出精确例子：
未来商可以闭合且有有限测试视界，
每个胞却含无限多个原始字面历史。
[[5](#bib-rooted)]

若未来允许精确查询原程序档案，
续卷 II §83 的列
$A_s(p)=\mathbf1_{p=s}$ 在任意 $n$ 个不同程序上产生 $I_n$，
故完整未来秩无穷。
这不与本节 $D^2$ 界矛盾：
增长档案已经扩展了被查询的角色和未来域，
不能在推导有限维终端闭包时偷偷删除。
[[2](#bib-continuation)]

<a id="section-8"></a>

## 8　从有界到衰减：递归误差的有限能量判据

新增 Datko 模块在实 Banach 空间的强连续收缩半群中，
证明每个向量的平方轨道可积，当且仅当有共同常数给统一指数稳定。
其证明先由一致有界原理取得统一有限窗口能量界，
再取得一个时刻的严格收缩，最后用半群律得到指数界。
[[4](#bib-datko)]
它要求的平方可积性不是归一化或酉性本身。

下面在三轴逻辑误差上给完整离散证明。
这个 Lyapunov 判据是标准线性系统理论，本稿的作用是明确接回 AURIC 的误差接口。
[[9](#bib-lyapunov)]

<a id="thm:energy"></a>

#### 定理 8.1（三轴逻辑误差的离散能量判据）

设 $T\in M_3(\mathbb R)$，误差按 $e_{n+1}=Te_n$ 更新。
以下条件等价：

1. 对每个 $e$，$\sum_{n\ge0}\|T^ne\|^2<\infty$；
2. 矩阵级数
   $P=\sum_{n\ge0}(T^n)^{\mathsf T}T^n$ 收敛；
3. 存在 $P\succ0$，满足 $T^{\mathsf T}PT=P-I$；
4. $T$ 的谱半径 $\rho(T)<1$。

此时 $P$ 唯一、$P\succeq I$，并且

$$
\boxed{
\|Te\|_P^2=\|e\|_P^2-\|e\|^2
\le q^2\|e\|_P^2,\qquad
q=\sqrt{1-\lambda_{\max}(P)^{-1}}<1.
}
$$

若 $q=0$ 则 $T=0$；否则得到共同指数界。

**证明。**

若对每个向量能量有限，分别用于三个标准基，
得到 $\sum_n\operatorname{Tr}[(T^n)^{\mathsf T}T^n]<\infty$。
各项正半定，其算子范数不超过迹，
所以矩阵级数绝对收敛且 $P\succeq I$。
移位求和给 $P-T^{\mathsf T}PT=I$。

反向，若有该正定 $P$，必有 $P\succeq I$；
又 $\|e\|^2\ge\|e\|_P^2/\lambda_{\max}(P)$，
得到所示收缩式。
迭代后由有限维范数等价给指数界，因而平方轨道可求和。
该指数界排除模至少为一的特征值。

若 $\rho(T)<1$，Jordan 块的幂是有限次多项式乘小于一的指数；
选介于谱半径与一之间的数，即得共同指数界，从而能量有限。
若 $P_1,P_2$ 都解该方程，差 $D$ 满足
$D=(T^n)^{\mathsf T}DT^n$，令 $n\to\infty$ 得 $D=0$。

**□**

<a id="statement-8-2"></a>

#### 推论 8.2（受迫误差的加权级数）

若 $e_{n+1}=Te_n+d_n$，则

$$
\boxed{
\|e_m\|_P
\le q^m\|e_0\|_P+
\sum_{j=0}^{m-1}q^{m-1-j}\|d_j\|_P.
}
$$

若 $\|d_j\|_P\le\delta$，则

$$
\limsup_{m\to\infty}\|e_m\|_P\le\frac{\delta}{1-q}.
$$

这是上极限界；有界驱动本身不保证受迫轨道收敛。

**证明。**

一步三角不等式给
$\|e_{n+1}\|_P\le q\|e_n\|_P+\|d_n\|_P$，
逐次代入。

**□**

$P^{1/2}$ 在这里定义误差度量，不被解释为免费原生酉门。
对于声明的 qubit CPTP 过程 $r\mapsto Tr+t$，
两个状态的差确实按同一个 $T$ 更新；
要对实际多轮使用该递推，仍须供应独立准备或充分记忆合同。
它不从一次过程表自动产生。

<a id="section-8-1"></a>

### 8.1　一步不严格收缩，仍可有稳定递归

考虑合法 CPTP 通道

$$
\Phi(\rho)
=
\langle0|\rho|0\rangle|+\rangle\langle+|
+
\langle1|\rho|1\rangle|-\rangle\langle-|.
$$

其 Kraus 算子为 $|+\rangle\langle0|$ 与 $|-\rangle\langle1|$，
满足保迹条件。
Bloch 作用为

$$
(r_x,r_y,r_z)\mapsto(r_z,0,0),\qquad
T=\begin{pmatrix}0&0&1\\0&0&0\\0&0&0\end{pmatrix}.
$$

所以 $\|T\|_{\mathrm{op}}=1$，但 $T^2=0$，两步后全部输入都到 $I/2$。
该例有

$$
P=I+T^{\mathsf T}T=\operatorname{diag}(1,1,2),
$$

直接满足 Lyapunov 方程。
因此 v38 使用的 $\|T\|<1$ 是方便的充分条件，
本轮的能量判据覆盖更多稳定逻辑过程。

另一方面，在定理 [6.4](#thm:isometry) 的完整未来闭合酉商上，
非零区别的固有范数保持，平方误差和必发散。
这里的“发散”是重复累计不衰减误差的能量，
不是态归一化失效，也不是单步误差变成无界。
逻辑通道的局部衰减与整体酉信息保留可以相容，
但须把转移到其他内部关系中的信息继续计入。

<a id="section-9"></a>

## 9　无限酉极限：强收敛与统一误差不同

新入库的 prime-layer 稿在相对全零真空的不完全无限张量积上，
让 $U_j$ 作用于不同内部新因子，
并在 $\sum_jb_j<\infty$ 下证明
$V_N=U_1\cdots U_N$ 及 $V_N^*$ 都强收敛，
所以极限为酉；它明确未声称算子范数收敛。
[[10](#bib-prime)]
这提供一种保持全部内部记录的正面模型，
也要求区别逐态极限与对所有输入统一的小误差。

<a id="thm:strong"></a>

#### 定理 9.1（平方可和的局部概率仍不保证算子范数收敛）

在上述同一零真空无限张量积空间上，取

$$
\theta_j=\frac1j,\qquad
b_j=\sin^2\theta_j,\qquad
U_j=
\begin{pmatrix}
\cos\theta_j&-\sin\theta_j\\
\sin\theta_j&\cos\theta_j
\end{pmatrix}
$$

作用于第 $j$ 个因子。
则 $\sum_jb_j<\infty$，$V_N,V_N^*$ 强收敛到互为伴随的酉，
但 $(V_N)$ 在算子范数下不是 Cauchy。

**证明。**

$\sin^2(1/j)\le1/j^2$，后者级数收敛。
对有限支撑向量 $\xi$、且 $M$ 超过其支撑，

$$
\|V_N\xi-V_M\xi\|^2
=
2\|\xi\|^2
\left(1-\prod_{j=M+1}^N\cos\theta_j\right)
\le2\|\xi\|^2\sum_{j>M}b_j.
$$

$\cos\theta_j=\sqrt{1-b_j}>0$，
最后用 $1-\prod\sqrt{1-b_j}\le\sum b_j$。
因此在稠密的有限支撑向量上 Cauchy；
酉范数一致有界，得全空间强收敛。
伴随有同一尾真空内积，故也强收敛。
若极限为 $V,A$，内积极限给 $A=V^*$，
一致有界性给 $VA=AV=I$。

对任意大的 $M$，调和级数发散，
可取最小 $N>M$ 使
$\Theta_{M,N}=\sum_{j=M+1}^N1/j\ge\pi/2$。
最小性给
$\Theta_{M,N}<\pi/2+1/(M+1)<\pi$。
在这一有限尾段上，取各 $U_j$ 特征值 $e^{i\theta_j}$
对应的张量积特征向量，其余尾因子仍为真空。
它属于同一个 Hilbert 空间，故

$$
\|V_N-V_M\|_{\mathrm{op}}
=\|U_{M+1}\cdots U_N-I\|_{\mathrm{op}}
\ge|e^{i\Theta_{M,N}}-1|
\ge\sqrt2.
$$

因此算子范数不 Cauchy。

**□**

该例未运行数值求和、截断枚举或搜索具体 $N$；
$N$ 仅由调和级数发散与极小元存在性指定，所有等式与界均为纸面证明。
它说明仅有 $\sum_j b_j<\infty$ 不足以推出算子范数收敛，
并未断言来源中的某个特定素数族必不范数收敛。
<!-- editorial-start:rotation -->
> **局部适用条件（编者说明）** 下述 $\|U_j-I\|_{\mathrm{op}}$ 等式沿用本例实二维旋转及 $\cos\theta_j=\sqrt{1-b_j}>0$ 的约定；$b_j$ 只给概率时，并不单独约束任意酉算符的相位或其在真空正交补上的作用。这里的加强条件不是对任意素数层酉族的结论。
<!-- editorial-end:rotation -->

若另有更强条件 $\sum_j\sqrt{b_j}<\infty$，则

$$
\|U_j-I\|_{\mathrm{op}}
=\sqrt{2(1-\sqrt{1-b_j})}\le\sqrt{2b_j},
$$

由酉乘积的望远镜估计即可得到算子范数 Cauchy 性。
强收敛对每个固定输入成立，
而算子范数允许随 $M,N$ 选择新的输入；
后者正是统一过程误差的更强量词。
无限数学内部因子的存在也不自动供应实际有限资源或原生控制权限。

<a id="section-10"></a>

## 10　本轮得到的可复合结论

本稿把三类 Gram 关系区分为：
输入关系 $G$ 决定秩退化；
后继响应 $\Gamma$ 决定未知质量的可识别性；
未来见证 $\mathsf G$ 决定完整预测坐标的误差标尺。
它们都可使用正关系与归一化表示，但不应互换最小特征值。

| 对象与目标 | 本轮结论 | 承重前件 |
| --- | --- | --- |
| 两设置记录质量 | 精确椭圆；最坏 $1/\kappa$ 阶锐利 | 指定投影后继与完整二分支质量 |
| 三原生设置 | 统一 $1/\sqrt\kappa$ 阶，且不可改善 | $B^2$ 的同输入统计与隔离合同 |
| 秩一目标权重 | 固定正 Lipschitz 模下 $\sqrt\epsilon$ 指数锐利 | 实际邻域、统一预算、同一记录规则 |
| 终端未来预测 | 有限字长闭合及 Gram 逆度量 | 固定完整载体、合法菜单、线性校准 |
| 酉闭合递归 | 可见关系度量等距 | 全部相关未来方向已保留 |
| 逻辑误差衰减 | 有限能量等价于 Lyapunov 严格收缩 | 同一可复合逻辑过程与驱动预算 |
| 无限内部记录 | 双向强极限酉；未必算子范数收敛 | 新因子、真空载体、具体收敛拓扑 |

对“两个读出加一个约束”的直觉，本轮的明确实例是
$\Delta A=\delta_1H_1-\delta_0H_0$：
归一化和指定后继把残差限制到二维平面，
两个适配读出便可分别消去对方权重。
若这些前件变动，维数也会变动。
对“递归始终保持酉性”的直觉，
未来闭合空间给出了正面等距定理；
局部误差真正衰减则由额外的能量与记忆条件负责。

<a id="bibliography"></a>

## 固定来源与证据范围

<a id="bib-head"></a>

**[1]**

The Omega Institute.
[固定公开提交 18ab178472d8c29](https://github.com/the-omega-institute/trureturing/commit/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84)。
本轮十八个取得记录、九个复用供应按固定树完成 Git blob 核对。
仅作公开只读获取、文本比较与纸面推导；未运行数学程序或 Lean。

<a id="bib-continuation"></a>

**[2]**

[AURIC：量子原则与相干重建续卷 II](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。
本轮文件未变；直接复核 §105、§111 的 $K_9,B,B^2$ 接口，
沿用 §§128–130 的未知质量、秩边界与记录连续性范围；
§77 的原生密度和 §83 的档案未来边界分别消费。
§111 三个设置的编号与本文幂次编号不同，正文已注明。

<a id="bib-v37"></a>

**[3]**

[二元关系、酉表示与黄金门通用性 v37](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
当前新增文件自述为先前作者稿转写，保留历史版本与证明陈述；
不是对本文或旧稿的独立新认证。
本稿不以源稿摘要代替数学阅读，也不认证当前本地 TeX 与转写输入的逐字同一性。

<a id="bib-datko"></a>

**[4]**

[DatkoStability.lean](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/D5/S3/Quantum/Analysis/DatkoStability.lean)。
完整阅读新公共声明
<code>integrab<wbr>le_sq_or<wbr>bit_iff_<wbr>exponent<wbr>ial_stab<wbr>ility</code>

及其证明源码。标量域为实数，载体为 Banach 空间，
前件为强连续收缩半群及各向量平方轨道可积。
未执行内核检查。

<a id="bib-rooted"></a>

**[5]**

[有根边界历史恢复](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md)，新增 §§11–14。
确定 floor 读口另行安装，原来源为正有理数且无复位、复制。
本稿消费未来等价、有限测试视界、原历史与实际取得的区别，
不移入其额外读口权限。

<a id="bib-v22"></a>

**[6]**

[相对门历史、观察商与递归闭合 v22](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，§8。
已有未来同余、黄金反例与最粗未来效果商是本文的前置供应；
本轮不将其重报为新结果。

<a id="bib-finiteword"></a>

**[7]**

[FiniteSequentialWordCertificate.lean](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate.lean)。
完整阅读字效果、有限证书及升链稳定的公开声明与证明。
一般实线性仪器对偶字以恒等效果为根；
本文的多个终端效果与纯酉菜单须另写其初始空间。

<a id="bib-controlled"></a>

**[8]**

[ControlledObservableCompletion.lean](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/D5/S3/Quantum/Dynamics/ControlledObservableCompletion.lean)。
公开定理给维数差闭合、未来等价与最小线性摘要，
但控制菜单为 Hamiltonian 等待，不能作为额外离散黄金门权限。

<a id="bib-lyapunov"></a>

**[9]**

Stephen Boyd.
[EE363：Linear quadratic Lyapunov theory](https://ee363.stanford.edu/archive/lectures/lq-lyap.pdf)，Winter 2008–09，
第 21–25 张。
本文第 8 节给标准离散判据的自足证明，并明确将其应用于逻辑误差，
不把该背景结果作为 AURIC 独有发现。

<a id="bib-prime"></a>

**[10]**

[素数层、贪心主导、反例终端与酉极限](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_PRIME_LAYER_GREEDY_DOMINANCE_COUNTEREXAMPLE_TERMINALS_AND_UNITARY_LIMIT.md)，§8。
本稿直接阅读其中新因子、不完全无限张量积、平方概率预算
以及双向强极限的完整小节。
源稿属于作者稿导入与编辑补充；其极限不声称算子范数收敛，
也不提供任意原生制备权限。

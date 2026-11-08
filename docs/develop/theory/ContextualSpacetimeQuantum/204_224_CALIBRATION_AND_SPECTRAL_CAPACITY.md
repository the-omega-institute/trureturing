# 情境时空算术的量子扩展：校准、谱纤维与尖锐容量

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](180_203_PROGRAM_INFORMATION.md) · [续卷](225_244_REAL_AND_COMPLEX_PROGRAMS.md)


<a id="entry-756"></a>

## 追加锚（本行以下为增补区）

<a id="section-204"></a>

## 204. 有限续接的椭圆完备性：三维环境与两参数精确优化

**定义 204.1（全域候选族及有限半径域）。** 固定 $0<a<1$。对 $-1<A,s<1$，定义
$$
\begin{gathered}
 B_A=\sqrt{1-A^2},\qquad d_s=1-s^2,\\
 x_{A,s}(u)=\frac{2a-A(1+u)+2(a-A)s}{B_A d_s},\qquad
 z_s(u)=\frac{u-s^2}{d_s},\\
 D_{A,s}(u)=d_s^2-
 \left[\frac{2a-A(1+u)+2(a-A)s}{B_A}\right]^2-(u-s^2)^2.
\end{gathered}
\tag{204.1}
$$
该程序的 Bloch 向量为 $(x_{A,s}(u),0,z_s(u))$，其满秩条件等价于 $D_{A,s}(u)>0$。对定义201.1的合法 $a,t,R$，记
$$
 \mathcal D_{a,t,R}=
 \{(A,s)\in(-1,1)^2:
 D_{A,s}(t-R)>0,\ D_{A,s}(t+R)>0\},
\tag{204.2}
$$
以及
$$
 \mathcal Q_{a,t}(A,s)=
 \frac{(1-s)^2-[2a-A(1+s)]^2}
 {(1-A^2)(1-s)^2D_{A,s}(t)}.
\tag{204.3}
$$
在（204.2）内，仿射曲线在闭区间内满秩，且可延拓到稍大的物理开区间。

**定理 204.2（任意二维精确程序的全域成本不增替代）。** 设一个固定 CPTP 处理器和一条 $C^1$ 二维程序曲线在非空开区间 $U\subset J_a$ 上，对所有信号输入精确生成 $\mathcal T_u$。则存在一对固定的 $A,s\in(-1,1)$，使定义204.1的程序在整个同一 $U$ 满秩、精确生成相同通道，并逐点满足
$$
 I_Q(\rho^{A,s}_u)\le I_Q(\rho_u)\qquad(u\in U).
\tag{204.4}
$$
替代处理器可取第203节的三维环境受控等距构造。因此对每个合法有限半径，
$$
 \boxed{\qquad
 \mathfrak M_2(a,t;R)=
 \inf_{(A,s)\in\mathcal D_{a,t,R}}
 \mathcal Q_{a,t}(A,s).
 \qquad}
\tag{204.5}
$$
若另外 $t\ge a$，则有限半径成本在抵达右侧完整边界时满足
$$
 \lim_{R\uparrow1-t}\mathfrak M_2(a,t;R)
 =B(a,t)=\frac{1-a^2}{(1-t)(1+t-2a^2)}.
\tag{204.6}
$$
式（204.5）是严格可行域上的下确界，不断言最小元存在；它也没有给出每个有限 $R$ 的最优参数闭式表达。（204.6）所用全区间上界 $B$ 已由定理190.2确立。

证明。 先用定理201.2，在同一处理器和同一 $U$ 上，把原程序替换为逐点成本不增的满秩仿射程序。其 Bloch 仿射线位于一个至多二维的线性平面内；用一个固定程序酉变换将它放到实 $XZ$ 平面。

在该满秩程序上，信号基态的纯输出迫使处理器具有受控等距形状。把处理器与其 Kraus 矩阵逐项复共轭所得的处理器平均，再与同时交换信号输入、输出基标号 $0,2$ 所得的处理器平均。这些都是固定 CPTP 处理器；实程序与目标 $F(a,u)$ 的实性及交换对称性保证它们保留所有输入上的目标通道，程序曲线及其成本也保持不变。复共轭 Kraus 构造不把反酉映射当作物理操作。

由受控表示，每个程序输入都给出 Schur 通道。对整个实 Bloch 圆盘，两个平均使其 Schur 矩阵都具有形式
$$
 F(\alpha,v)=
 \begin{pmatrix}1&\alpha&v\\\alpha&1&\alpha\\v&\alpha&1\end{pmatrix},
\tag{204.7}
$$
其中 $\alpha,v$ 为圆盘坐标的实仿射函数。该矩阵正半定等价于
$$
 2\alpha^2\le1+v\le2.
\tag{204.8}
$$
故令 $x=\alpha$、$y=(1+v)/2$，圆盘的仿射像是抛物线段
$$
 P=\{(x,y):x^2\le y\le1\}
\tag{204.9}
$$
内的椭圆或退化椭圆，记为 $E$。它包含所有目标点 $(a,(1+u)/2)$，所以其仿射维数至少为一。

下面在本证明内确定覆盖 $E$ 所需的椭圆。第203节的等距公式只使用 $A^2+B_A^2=1$ 和 $s^2+(\sqrt{1-s^2})^2=1$，所以对任意 $|A|,|s|<1$ 都定义实际处理器，不限于临界邻域。它在整个实 Bloch 圆盘上的像为
$$
\begin{aligned}
 x&=\frac{A(1+s)}2+
 \frac{1-s}{2}\bigl(\sqrt{1-A^2}\,r_x+Ar_z\bigr),\\
 y&=\frac{1+s^2}{2}+\frac{1-s^2}{2}r_z.
\end{aligned}
\tag{204.10}
$$
令 $\tau=1/(1+s)>1/2$、$w=1-y$，这个椭圆的内域由
$$
 Q_{A,\tau}(x,y)=
 (x-A)^2+2A\tau(x-A)w+\tau^2w^2
 -(1-A^2)(2\tau-1)w\le0
\tag{204.11}
$$
给出；代入（204.10），左边恰为
$(1-A^2)(1-s)^2(r_x^2+r_z^2-1)/4$。其两个边界限制为
$$
 Q_{A,\tau}(x,1)=(x-A)^2,
 \qquad
 Q_{A,\tau}(x,x^2)=
 [\tau x^2-Ax+1-\tau]^2.
\tag{204.12}
$$

若 $E$ 非退化，在包含 $E$ 且位于 $P$ 内的椭圆中取面积最大者 $E_* $。这样的最大者存在：椭圆中心与半轴由紧集 $P$ 一致控制，而包含一个固定非退化椭圆给出最小半轴的一致正下界；用正定形状矩阵表示后，可行集合闭且有界。面积最大者也是按包含关系的极大者。

写 $E_* =\{Q\le0\}$，其中 $Q$ 的二次齐次部分正定。它不能经过 $P$ 的两个角点 $(\pm1,1)$：角点处有两条不同的支撑直线，而非退化椭圆在边界点只有一条支撑直线。椭圆与抛物线的接触都位于 $-1<x<1$，且 $Q(x,x^2)$ 是首项系数为正的四次多项式，在实轴上非负。因此它至多有两个不同实根；每个实根的重数为二或四。

极大者必接触上盖 $y=1$，并且抛物线接触的总重数必为四。为验证这一步，记
$$
 L_r(x,y)=y-2rx+r^2,\qquad L_c(x,y)=1-y.
\tag{204.13}
$$
它们在 $P$ 内均非负，$L_r$ 是抛物线在 $r$ 的切线因子。若上盖尚有严格余量，且抛物线有两个二重接触 $r_1,r_2$，则用
$Q-\varepsilon L_{r_1}L_{r_2}$ 替换 $Q$；在抛物线上仅减小
$(x-r_1)^2(x-r_2)^2$ 的正系数。若只有一个四重接触，用 $Q-\varepsilon L_r^2$；若只有一个二重接触，同一扰动的四阶消失仍被原二阶正余量控制；若没有接触，用 $Q-\varepsilon$。充分小的正 $\varepsilon$ 保持二次部分正定、抛物线上的非负性及上盖的严格余量，却严格扩大椭圆。

若已经接触上盖而没有抛物线接触，使用 $Q-\varepsilon L_c^2$。若上盖之外只有一个二重抛物线接触 $r$，使用
$$
 Q-\varepsilon L_cL_r.
\tag{204.14}
$$
在上盖上该扰动为零，在抛物线上它为
$-\varepsilon(1-x^2)(x-r)^2$；原限制除以 $(x-r)^2$ 后在 $[-1,1]$ 上有严格正下界，所以小扰动仍非负。各次扰动在旧椭圆内减去非负量，并在部分边界上严格减小，故确实给出严格包含。新椭圆仍含有旧内点；它不能跨越上盖或抛物线，否则跨越处会有边界曲线上的点进入 $Q_{\rm new}<0$，与上述非负性矛盾。这些严格扩大均与极大性冲突，所需接触形状得证。

于是上盖相切于某个 $(A,1)$、$|A|<1$。归一化 $Q$ 使
$Q(x,1)=(x-A)^2$。总重数四说明
$Q(x,x^2)=p(x)^2$，其中 $p$ 是实二次多项式，其两个根按重数计算都在 $(-1,1)$。在 $\pm1$ 的值同号；选取正号后，
$$
 p(1)=1-A,\qquad p(-1)=1+A,
 \qquad p(x)=\tau x^2-Ax+1-\tau.
\tag{204.15}
$$
比较两条限制便得到 $Q=Q_{A,\tau}$：两个二次式在抛物线上的差为零时，其差只能是 $y-x^2$ 的常数倍，而上盖限制将该倍数固定为零。椭圆在上盖下方有内点，所以（204.11）中沿向下方向的一阶系数为负，即
$(1-A^2)(2\tau-1)>0$。故 $\tau>1/2$，并对应某个 $s=1/\tau-1\in(-1,1)$。这证明每个非退化 $E\subset P$ 都被（204.10）的某个实际处理器椭圆包含。

若 $E$ 退化，它必须是竖直线段 $x=a$，因为其中有非恒定的目标直线。它位于 $a^2\le y\le1$。取 $A=a,s=0$ 即可包含整段；沿该竖线的程序为
$$
 r_x(u)=\frac{a(1-u)}{\sqrt{1-a^2}},\qquad r_z(u)=u,
\qquad
 1-|r(u)|^2=
 \frac{(1-u)(u-(2a^2-1))}{1-a^2}\ge0
\tag{204.16}
$$
对 $2a^2-1\le u\le1$ 成立。故退化情况也有同一构造族的覆盖。

还须把几何包含转成信息成本比较。设旧圆盘像映射为 $c+Mr$，包含它的新椭圆映射为 $c_*+M_*r$，其中 $M_*$ 可逆。仿射变换
$$
 T(r)=M_*^{-1}(c+Mr-c_*)
\tag{204.17}
$$
把实单位圆盘送入自身，并把旧程序的目标像送到新程序的同一目标像。把任意 Bloch 向量先投影到 $XZ$ 平面，再作用 $T$，得到一个正、保迹的量子比特线性映射 $\Lambda$。这里仅用它定义另一族已知程序制备并比较成本，不声称它是对未知程序可物理实施的 CPTP 变换。

对于任意正保迹的量子比特映射，点态 SLD 信息在满秩处不增。此处可直接用变分公式证明：
$$
 I_Q(\rho,\dot\rho)=
 \sup_{L=L^\dagger}
 \{2\operatorname{Tr}(\dot\rho L)-\operatorname{Tr}(\rho L^2)\}.
\tag{204.18}
$$
对偶 $\Lambda^*$ 为正的幺映射。将任意二维 Hermitian 矩阵写成 $L=cI+dV$、$V^2=I$，由
$-I\preceq\Lambda^*(V)\preceq I$ 得
$$
 \Lambda^*(L^2)-\Lambda^*(L)^2
 =d^2[I-\Lambda^*(V)^2]\succeq0.
\tag{204.19}
$$
代回（204.18），每个输出试验矩阵的值都不超过输入端取 $\Lambda^*(L)$ 的值，故
$I_Q(\Lambda\rho,\Lambda\dot\rho)\le I_Q(\rho,\dot\rho)$。

旧程序在 $U$ 内满秩。若旧圆盘像非退化，它的目标点位于旧椭圆内部，因此也位于新椭圆内部。若像为竖直线段，由 $U\subset J_a\subset(2a^2-1,1)$ 及（204.16）同样得到严格内部性。故新程序在整个同一 $U$ 满秩。它由（204.17）给出仿射曲线；解（204.10）的目标条件 $x=a,y=(1+u)/2$，恰得（204.1）。第203节提供三维环境的实际固定处理器，并保证对全部信号输入精确。因此（204.4）成立，也没有缩小原开域。

每个原问题可行程序都被这样替代，而族内每个满足（204.2）的参数本身可行，所以有限半径的两个下确界相同。计算其名义成本，记
$$
 p=\frac{2a-A(1+s)}{B_A(1-s)},\qquad
 x_{A,s}(u)+\frac A{B_A}z_s(u)=p.
\tag{204.20}
$$
对实平面仿射线，Bloch 公式给出
$$
 I_Q=
 \frac{|r'|^2-(r_xr_z'-r_zr_x')^2}{1-|r|^2}.
\tag{204.21}
$$
此处 $|r'|^2=1/(B_A^2d_s^2)$、叉积为 $p/d_s$，代入即得（204.3）、（204.5）。所有分母都在严格可行域内为正。

最后证明（204.6）。参数 $A=a,s=0$ 在整个 $J_a$ 可行，并由（204.3）给出 $B(a,t)$；这也与定理190.2的既有全区间结算相符。故所有合法有限半径都有成本上界 $B$。取任意 $R_n\uparrow1-t$，选取距（204.5）下确界趋于零的族内可行元。两端点正性给出
$$
 |r(t)|^2+R_n^2|r'|^2<1,
 \qquad B_A(1-s^2)>R_n.
\tag{204.22}
$$
因此 $A,s$ 沿子列收敛于 $(-1,1)^2$ 内部，并且名义状态保持一致满秩。在上端点极限 $u=1$，有 $z_s(1)=1$，所以状态正性迫使
$$
 x_{A,s}(1)=\frac{2(a-A)}{B_A(1-s)}=0,
 \qquad A=a.
\tag{204.23}
$$
在这个极限上，名义成本连续，并简化为
$$
 \mathcal Q_{a,t}(a,s)
 =\frac1{(1-t)\left[
 (1+t-2a^2)/(1-a^2)-2s^2\right]}
 \ge B(a,t).
\tag{204.24}
$$
名义一致满秩保证括号为正。上、下界合并即得（204.6）。条件 $t\ge a$ 恰保证 $R\uparrow1-t$ 时仍可从合法对称半径域内趋近；对其他 $t$ 不作该边界极限断言。证毕。

<a id="entry-758"></a>

## 追加锚（本行以下为增补区）

<a id="section-205"></a>

## 205. 有限最优值与真实可达性的分离：紧松弛、全超临界不达到与单变量归约

**定义 205.1（有限半径的非严格端点域）。** 固定定义201.1的合法 $a,t,R$，沿用定义204.1的候选程序，置
$$
\begin{aligned}
 f_{A,s}(u)&=(1-A^2)(1-u)(1+u-2s^2)
 -[2a(1+s)-A(1+u+2s)]^2,\\
 g_{A,s}&=(1-s)^2-[2a-A(1+s)]^2,\\
 q(A,s)&=\frac{g_{A,s}}{(1-s)^2f_{A,s}(t)}.
\end{aligned}
\tag{205.1}
$$
于是 $f_{A,s}(u)=(1-A^2)D_{A,s}(u)$，且 $q=\mathcal Q_{a,t}$。记严格域为 $\mathcal D_R=\mathcal D_{a,t,R}$，并定义
$$
 \mathcal K_R=\{(A,s)\in(-1,1)^2:
 f_{A,s}(t-R)\ge0,\ f_{A,s}(t+R)\ge0\}.
\tag{205.2}
$$
$\mathcal K_R$ 只要求两个端点状态为正半定，不先赋予其成员在闭区间外的开放延拓。

**定理 205.2（紧松弛的精确性与任意超临界半径的不达到性）。** 集合 $\mathcal K_R$ 非空且紧，$q$ 在其上连续，并且
$$
 \boxed{\quad
 \mathfrak M_2(a,t;R)=\inf_{\mathcal D_R}q
 =\min_{\mathcal K_R}q.
 \quad}
\tag{205.3}
$$
原问题的最优值可由实际程序达到，当且仅当 $\mathcal K_R$ 中存在一个两个端点约束都严格的最小元。结合定义201.1及定理201.3的 $R_0(a,t)$，真实可达性完整分类为
$$
\begin{array}{c|c|c}
 \text{合法半径}&\mathfrak M_2(a,t;R)&\text{原程序类是否有最小元}\\ \hline
 R<R_0&I_r(t)&\text{有}\\
 R=R_0&I_r(t)&\text{无}\\
 R>R_0&>I_r(t)&\text{无}.
\end{array}
\tag{205.4}
$$
每行仍以该半径满足（201.1）为前提。特别地，在任意合法 $R\ge R_0$，每个松弛最小元至少有一个端点约束取等；尽管这些最小元存在，原问题中没有任何固定 CPTP 处理器及 $C^1$ 二维程序达到该成本，包括允许秩变化的程序。

证明。 先证明紧性和名义分母不退化。参数 $A=a,s=0$ 在全部 $J_a$ 上严格可行，所以两个集合非空。对 $\mathcal K_R$ 中的一个参数，将（204.1）的 Bloch 仿射线记为 $r(u)$。端点正性给出
$$
 |r(t)|^2+R^2|r'|^2
 =\frac{|r(t-R)|^2+|r(t+R)|^2}{2}\le1,
 \qquad |r'|^2=\frac1{(1-A^2)(1-s^2)^2}.
\tag{205.5}
$$
因此
$$
 \sqrt{1-A^2}(1-s^2)\ge R,
 \qquad |A|\le\sqrt{1-R^2},\qquad
 |s|\le\sqrt{1-R}.
\tag{205.6}
$$
合法半径满足 $0<R<1$，故这些界将整个集合限制在 $(-1,1)^2$ 内的一个紧矩形；多项式端点约束是闭的。另有
$$
 \frac{d^2}{du^2}f_{A,s}(u)=-2,
 \qquad
 f_{A,s}(t)=\frac{f_{A,s}(t-R)+f_{A,s}(t+R)}2+R^2
 \ge R^2>0.
\tag{205.7}
$$
于是 $q$ 连续，松弛最小元存在。

关键是证明严格下确界与该最小值相同，而不是仅把严格符号改成非严格符号。取任意 $(A,s)\in\mathcal K_R$，以（204.11）表示它的椭圆二次式 $Q_0$。令 $Q_1=Q_{a,1}$，即参数 $A=a,s=0$ 的严格可行椭圆；这里 $Q$ 的第二指标为 $\tau=1/(1+s)$。两个目标端点
$$
 p_\pm=\left(a,\frac{1+t\pm R}{2}\right)
\tag{205.8}
$$
满足 $Q_0(p_\pm)\le0$、$Q_1(p_\pm)<0$。对 $0<\varepsilon<1$ 定义
$$
 Q_\varepsilon=(1-\varepsilon)Q_0+\varepsilon Q_1.
\tag{205.9}
$$
其二次部分正定，在抛物线帽 $P$ 的整个边界上非负，而在两个目标端点严格为负。由定理204.2证明中的边界穿越论证，$E_\varepsilon=\{Q_\varepsilon\le0\}$ 是位于 $P$ 内的非退化椭圆，且两个端点都在其内部。

可连续选取圆盘参数化 $c_\varepsilon+M_\varepsilon r$，使其在 $\varepsilon\downarrow0$ 时趋向原椭圆的参数化：取椭圆形状矩阵的正平方根，再右乘固定的正交因子，使 $\varepsilon=0$ 时等于原 $M_0$。沿目标直线取逆像，所得 Bloch 仿射程序及其导数都收敛到原程序。由（205.7）原名义态满秩，所以这些程序在名义点的 SLD 成本收敛到 $q(A,s)$。

应用定理204.2证明中的椭圆包含引理，把每个 $E_\varepsilon$ 扩为一个显式族的包含椭圆。两个目标端点仍严格在内部。圆盘之间的正保迹映射与 SLD 变分比较给出不更大的名义成本；最终椭圆由第203节的实际固定处理器实现。因此得到 $\mathcal D_R$ 内的程序，其成本上极限不超过 $q(A,s)$。中间椭圆只用于构造和比较，不需要把它另行认作实际处理器的像。对松弛最小元应用这一论证，得
$$
 \inf_{\mathcal D_R}q\le\min_{\mathcal K_R}q.
\tag{205.10}
$$
反向由集合包含立即得到；定理204.2遂给出（205.3）。该论证同时处理两个端点取等，不需要预设仅有上端点活跃，也不宣称 $\mathcal K_R$ 的每个参数本身具有开放延拓。

若松弛最小元位于 $\mathcal D_R$，其显式程序可在稍大开域精确实现，所以原问题达到。反过来，若任意原程序达到最优值，定理204.2给出一个 $\mathcal D_R$ 内的替代程序，成本不增；由下确界定义它仍达到最优值，故为严格的松弛最小元。这证明可达性等价。

最后排除所有超临界最小元。名义点的严格物理参数域内置
$$
\begin{gathered}
 b=1+s,\quad j=1-s,\quad
 c=(1-t)(1+t-2s^2),\\
 L=1+t-2s,\quad J=1+t-2a^2,\quad f=f_{A,s}(t),\\
 F_1=bLA-2a(t-s^2),\qquad
 F_2=2abA-4a^2+L.
\end{gathered}
\tag{205.11}
$$
这里 $b,j,J,f,c$ 均为正：特别地，$f>0$ 及（205.1）迫使 $c>0$。直接展开给出两个平方分解及导数分解
$$
\begin{aligned}
 q&=\frac1c+\frac{F_1^2}{j^2fc},\\
 q&=\frac1{2Jj^2}+\frac{F_2^2}{2Jj^2f},\\
 \partial_Aq&=\frac{2bF_1F_2}{j^2f^2}.
\end{aligned}
\tag{205.12}
$$
故 $A$ 方向驻点必满足 $F_1=0$ 或 $F_2=0$。在各零集上，平方项对 $s$ 的偏导也为零，因此分别有
$$
 F_1=0\Longrightarrow\partial_sq=\frac{4s(1-t)}{c^2},
 \qquad
 F_2=0\Longrightarrow\partial_sq=\frac1{J(1-s)^3}>0.
\tag{205.13}
$$
第二支不含二维驻点；第一支只有
$$
 s=0,\qquad A=\frac{2at}{1+t},\qquad q=\frac1{1-t^2}=I_r(t).
\tag{205.14}
$$
所以任何严格可行域上的最小元都必须具有成本 $I_r(t)$，因为 $\mathcal D_R$ 为开集。定理201.3在 $R\ge R_0$ 排除了这样的实际达到；在 $R>R_0$ 还给出严格正差距。由可达性等价，全部临界及超临界半径均无原问题最小元。亚临界达到沿用定理201.3，合成（205.4）。证毕。

**定理 205.3（有限成本的单变量精确求值）。** 置
$$
 y_\pm=\frac{1+t\pm R}{2},
 \qquad
 A_\pm(y,s)=
 \frac{a(y+s)\pm\sqrt{(1-y)(y-s^2)(y-a^2)}}{y(1+s)}.
\tag{205.15}
$$
对 $|s|<\sqrt{y_-}$ 定义
$$
 \ell_s=\max\{A_-(y_-,s),A_-(y_+,s)\},\qquad
 h_s=\min\{A_+(y_-,s),A_+(y_+,s)\},
\tag{205.16}
$$
并令 $\mathcal S_R$ 为其中满足 $\ell_s<h_s$ 的全部 $s$。对 $s\in\mathcal S_R$，令有限集合 $\mathcal C_s$ 含 $\ell_s,h_s$，并加入下列落在 $[\ell_s,h_s]$ 内的数：
$$
 A^{(1)}(s)=\frac{2a(t-s^2)}{(1+s)(1+t-2s)},\qquad
 A^{(2)}(s)=\frac{4a^2-(1+t-2s)}{2a(1+s)}.
\tag{205.17}
$$
若 $1+t-2s=0$，不加入 $A^{(1)}$。则 $\mathcal S_R$ 非空，所有这些求值均有正的名义分母，且
$$
 \boxed{\qquad
 \mathfrak M_2(a,t;R)
 =\inf_{s\in\mathcal S_R}\ \min_{A\in\mathcal C_s}q(A,s).
 \qquad}
\tag{205.18}
$$
每个 $s$ 至多需要四个候选值。端点候选按严格可行程序的极限求值，不能仅因它们出现在公式中便将其计为原问题的实际最优程序。

证明。 合法半径给出 $a<y_-<y_+<1$。在固定端点 $u=2y-1$，式（205.1）变为
$$
 \frac14 f_{A,s}(2y-1)
 =(1-A^2)(1-y)(y-s^2)-[a(1+s)-A(y+s)]^2.
\tag{205.19}
$$
若左边严格为正，必有 $s^2<y$。反过来，固定 $|s|<\sqrt{y}$，右边关于 $A$ 为严格凹二次式，二次项系数为 $-y(1+s)^2$，两根恰为（205.15）。其严格正区间为 $A_-(y,s)<A<A_+(y,s)$；由（205.19），该区间自动位于 $(-1,1)$。两端点条件的交集因此正好是
$$
 s\in\mathcal S_R,\qquad \ell_s<A<h_s.
\tag{205.20}
$$
$A=a,s=0$ 提供非空性。

在固定 $s\in\mathcal S_R$，闭区间 $[\ell_s,h_s]$ 属于 $\mathcal K_R$，故由（205.7）名义分母严格为正。连续函数在该闭区间的最小值等于在其开内部的下确界。内部最小元满足 $\partial_Aq=0$；由（205.12），它只能来自（205.17）的两支。若 $L=1+t-2s=0$，则
$$
 t-s^2=-\frac{(1-t)^2}{4}<0,
\tag{205.21}
$$
所以 $F_1$ 为非零常数，不遗漏第一支的驻点。第二支的分母总为正。连同两个端点，便得到集合 $\mathcal C_s$。逐 $s$ 取下确界并应用（204.5）即得（205.18）。这里没有求出剩余标量下确界的闭式，也没有把双端点的交集预先替换成单个端点约束。证毕。

<a id="entry-760"></a>

## 追加锚（本行以下为增补区）

<a id="section-206"></a>

## 206. 有限续接成本的精确解：唯一上端接触与可认证的八次根

**定义 206.1（上端接触的无量纲坐标）。** 固定定义201.1的合法 $a,t,R$，并假定 $R>R_0(a,t)$。置
$$
\begin{gathered}
 h=\frac{1+t}{2},\qquad z=\frac{1+t+R}{2},\qquad
 \Delta=z-h=\frac R2,\qquad k=1-a^2,\\
 \alpha=\sqrt{\frac{z-a^2}{k}},\qquad
 \beta=\sqrt{\frac{h-a^2}{k}},\qquad
 \sigma=\sqrt{1-\alpha^2}=\sqrt{\frac{1-z}{k}},\qquad
 \xi_b=\frac{a\sigma}{\sqrt z}.
\end{gathered}
\tag{206.1}
$$
合法性给出 $a<h<z<1$，以及
$0<\xi_b<\beta<\alpha<1$、$\xi_b<\sigma$。对 $0\le\xi\le\xi_b$ 定义
$$
\begin{gathered}
 \delta(\xi)=\operatorname{artanh}\alpha-\operatorname{artanh}\xi,\qquad
 C(\xi)=\cosh\delta(\xi),\quad S(\xi)=\sinh\delta(\xi),\\
 W(\xi)=\frac{S(\xi)(C(\xi)+a)}{1+aC(\xi)},\qquad
 \Phi(\xi)=\xi^2+\xi(1-\xi^2)W(\xi).
\end{gathered}
\tag{206.2}
$$
这些量只用于参数化同一个有限程序优化问题，不改变点态 SLD 信息的定义或精确开放延拓条件。

**定理 206.2（全部超临界半径的唯一代数最优设计）。** 方程
$$
 \Phi(\xi_*)=\beta^2,\qquad 0<\xi_*<\xi_b
\tag{206.3}
$$
恰有一个解。令 $r_*=\sqrt{1-\xi_*^2}$，并定义
$$
 s_*=\alpha\xi_*-a\sigma r_*,\qquad
 A_*=\frac{a(1+\alpha\xi_*)-\sigma r_*}
 {1+\alpha\xi_*-a\sigma r_*}.
\tag{206.4}
$$
则 $(A_*,s_*)$ 是定义205.1的紧松弛问题的唯一最小元，原始开放延拓问题的精确下确界为
$$
 \boxed{\quad
 \mathfrak M_2(a,t;R)=
 \frac{(\alpha-\xi_*)^2}
 {4\Delta(\beta^2-\xi_*^2)
 (1-\alpha\xi_*+a\sigma r_*)^2}.
 \quad}
\tag{206.5}
$$
该最小元只在上端点接触物理边界。更精确地，置
$$
 \ell_*=a^2+k\xi_*^2;
\tag{206.6}
$$
则它的物理区间在 $y=(1+u)/2$ 坐标中的两个根为 $\ell_*,z$，且
$$
 \ell_*<\frac{a^2}{z}<a,
 \qquad
 f_{A_*,s_*}(t+R)=0,
 \qquad
 f_{A_*,s_*}(t-R)>0,
 \qquad s_*<0.
\tag{206.7}
$$
唯一性指显式族中的参数对，不要求不同物理处理器的实现唯一。原问题仍不达到这个下确界；存在定义204.1的严格可行程序列，其名义成本收敛到（206.5）。

证明。 先将所有处理器经定理204.2归约到显式族。为求下界，暂时仅保留名义点正性和上端点正性。置
$$
 v=A(1+s)-a,
 \qquad
 H_y(s,v)=\frac14f_{A,s}(2y-1).
\tag{206.8}
$$
直接展开得到
$$
 H_y=(1-y)(y-a^2)-(1+a^2-y)s^2+2asv-yv^2.
\tag{206.9}
$$
对每个 $a<y<1$，$H_y\ge0$ 是 $(s,v)$ 平面中的一个中心椭圆。目标函数变成
$$
 q_h(s,v)=\frac{g(s,v)}{4(1-s)^2H_h(s,v)},\qquad
 g(s,v)=(1-s)^2-(a-v)^2.
\tag{206.10}
$$
考虑放大后的集合 $H_h>0,H_z\ge0$。它确实有最小元，且没有通过名义秩退化逃逸的低成本序列。为此记
$$
 c_0=s+a^2-av,
 \qquad H_y=g(y-a^2)-(y-c_0)^2.
\tag{206.11}
$$
在紧交集 $H_h\ge0,H_z\ge0$ 上，$g$ 严格为正；否则 $h=c_0=z$，与 $h<z$ 矛盾。由 $H_h\ge0$ 的椭圆式还得 $|s|\le\sqrt h<1$。因而在该紧集上 $g$ 有一致正下界，而 $q_h$ 在 $H_h\downarrow0$ 时趋于正无穷。集合非空且有有限成本，例如 $s=v=0$。所以放大问题取得有限最小值。

上述集合也没有引入非物理的内部参数：以 $A=(a+v)/(1+s)$ 回代，$H_h>0$ 由（205.19）迫使 $|A|<1$；对闭交集中的 $A=\pm1$，两个不同 $y$ 的正性会要求同一个非恒定一次式同时为零，不可能。坐标变换在此光滑可逆。由（205.12）—（205.14），若放大问题最小元满足 $H_z>0$，它只能是名义等号参数
$$
 s=0,\qquad A=2a-\frac ah.
\tag{206.12}
$$
但 $R>R_0$ 时，这个参数不满足上端点正性。因此所有放大问题最小元均在 $H_z=0$ 上。

完整参数化这条接触椭圆。定义
$$
 p=\frac{s-av}{k},\qquad w=\frac{v-as}{k}.
\tag{206.13}
$$
式（206.9）在 $y=z$ 等价于
$$
 H_z=k^2\alpha^2\sigma^2
 \left(1-\frac{p^2}{\alpha^2}-\frac{w^2}{\sigma^2}\right).
\tag{206.14}
$$
故全部上端接触点均可写成
$$
 \begin{aligned}
 s&=\alpha\xi+\tau a\sigma\sqrt{1-\xi^2},\\
 v&=a\alpha\xi+\tau\sigma\sqrt{1-\xi^2},
 \end{aligned}
 \qquad -1\le\xi\le1,\quad \tau\in\{-1,1\}.
\tag{206.15}
$$
代入给出两个精确恒等式
$$
 H_y=(z-y)(y-\ell(\xi)),\qquad
 \ell(\xi)=a^2+k\xi^2,\qquad
 g=k(\alpha-\xi)^2.
\tag{206.16}
$$
名义正性因此恰为 $|\xi|<\beta$，接触边界上的成本为
$$
 q_{h,\tau}(\xi)=
 \frac{(\alpha-\xi)^2}
 {4\Delta(\beta^2-\xi^2)
 (1-\alpha\xi-\tau a\sigma\sqrt{1-\xi^2})^2}.
\tag{206.17}
$$
这里两个符号分支的 $1-s$ 均为正。固定 $\xi$，取 $\tau=-1$ 严格增大分母，因此严格减小成本。令
$$
 P(\xi)=1-\alpha\xi+a\sigma\sqrt{1-\xi^2},
 \qquad q_h(\xi)=q_{h,-1}(\xi).
\tag{206.18}
$$
对 $0<\xi<\beta$，交叉相乘可验证
$$
 \frac{\alpha-\xi}{P(\xi)}
 <\frac{\alpha+\xi}{P(-\xi)};
\tag{206.19}
$$
两侧交叉分子的差为
$2\xi(\alpha^2-1-a\sigma\sqrt{1-\xi^2})<0$。故正 $\xi$ 严格优于负 $\xi$。此外
$$
 \left.\frac12\frac{d}{d\xi}\log q_h(\xi)\right|_{\xi=0}
 =-\frac1\alpha+\frac{\alpha}{1+a\sigma}<0.
\tag{206.20}
$$
于是所有最小元都属于 $\tau=-1,0<\xi<\beta$，这些选择来自成本比较而非预设对称性。

下面在求驻点之前排除下端点接触。固定 $z>a$，置
$$
 K_z=\sqrt{\frac{(1-z)(z-a^2)}z},\qquad
 h_c=\frac{a}{a+K_z}.
\tag{206.21}
$$
有 $a<h_c<z$：分别平方 $K_z<1-a$ 和 $a(1-z)<zK_z$ 后，两者均归结为 $z>a$。名义等号参数（206.12）的上端点条件为
$$
 H_z=z\left[K_z^2-\frac{a^2(1-h)^2}{h^2}\right].
\tag{206.22}
$$
因此本问题的超临界条件恰为 $h<h_c$。在 $\xi=\xi_b$，有
$$
 \sqrt{1-\xi_b^2}=\frac\alpha{\sqrt z},\qquad
 s=0,\quad v=-K_z,\quad A=a-K_z=2a-\frac a{h_c},\quad
 \ell(\xi_b)=\frac{a^2}{z}<a.
\tag{206.23}
$$
这是名义点 $2h_c-1$ 的等号程序，并且该名义点处于其满秩区间内。

对 $\xi_b\le\xi<\beta$，在同一个上端接触处理器上比较名义点 $h,h_c$。由（206.16），
$$
 \frac{q_h(\xi)}{q_{h_c}(\xi)}
 =\frac{z-h_c}{z-h}\,
 \frac{h_c-\ell(\xi)}{h-\ell(\xi)}.
\tag{206.24}
$$
最后一个因子关于 $\ell$ 严格递增，因为其导数为
$(h_c-h)/(h-\ell)^2>0$。另一方面，在名义点 $h_c$，测量信息下界及（206.23）给出
$q_{h_c}(\xi)\ge q_{h_c}(\xi_b)$。故
$$
 q_h(\xi)>q_h(\xi_b)\qquad(\xi_b<\xi<\beta).
\tag{206.25}
$$
在 $\xi_b$ 本身，名义等号使 $q_{h_c}'(\xi_b)=0$。微分（206.24）得
$$
 \frac{q_h'(\xi_b)}{q_h(\xi_b)}
 =\frac{2k\xi_b(h_c-h)}
 {(h_c-\ell(\xi_b))(h-\ell(\xi_b))}>0.
\tag{206.26}
$$
向左移动即可改善。因此所有全局最小元都落在 $0<\xi<\xi_b$。在这一区间，$s=\alpha\xi-a\sigma\sqrt{1-\xi^2}<0$，且
$\ell(\xi)<a^2/z<a$。原问题的下端点 $y_-=h-R/2>a$ 已严格位于物理区间内部；这个结论没有被用作选根的预设条件。

最后证明剩余根的唯一性。由（206.2），
$$
 C=\frac{1-\alpha\xi}{\sigma\sqrt{1-\xi^2}},\qquad
 S=\frac{\alpha-\xi}{\sigma\sqrt{1-\xi^2}},\qquad
 q_h(\xi)=\frac{S^2}{4\Delta(\beta^2-\xi^2)(C+a)^2}.
\tag{206.27}
$$
因此
$$
 \frac12\frac{d}{d\xi}\log q_h
 =\frac{\xi}{\beta^2-\xi^2}-\frac1{(1-\xi^2)W}.
\tag{206.28}
$$
其符号恰为 $\Phi(\xi)-\beta^2$ 的符号。下面给出 $\Phi'>0$ 的显式证书。记
$$
 \omega=\tanh\delta=\frac{\alpha-\xi}{1-\alpha\xi}.
\tag{206.29}
$$
在 $0\le\xi\le\xi_b<\sigma$ 上，$\alpha^2+\xi^2<1$，所以
$$
 1-3\xi\omega
 =\frac{1-\alpha^2-\xi^2+(\alpha-2\xi)^2}{1-\alpha\xi}>0.
\tag{206.30}
$$
定义
$$
\begin{aligned}
 N_0&=\frac{(\xi+\omega)(1-3\xi\omega)}{1-\omega^2}>0,\\
 N_2&=N_0+4\xi S^2>0,\\
 N_1&=\frac{C^2+1}{C}N_0+
 \frac{\xi S^2(C^2+3)}C>0.
\end{aligned}
\tag{206.31}
$$
利用 $\delta'=-1/(1-\xi^2)$ 微分并整理，得到
$$
 \Phi'(\xi)=\frac{N_0+aN_1+a^2N_2}{(1+aC)^2}>0.
\tag{206.32}
$$
又 $\Phi(0)=0$，而在比较名义点 $h_c$，$\xi_b$ 为内部名义等号点；由（206.28）得
$$
 \Phi(\xi_b)=\frac{h_c-a^2}{k}>
 \frac{h-a^2}{k}=\beta^2.
\tag{206.33}
$$
严格单调性与介值定理给出唯一根 $\xi_*$；成本在它之前递减、之后递增。（206.25）及两个严格分支比较排除了其余所有全局最小元，于是放大问题的唯一最小元恰为（206.4）。

仍须回到原始开放延拓问题。令
$$
 v_*=a\alpha\xi_* -\sigma r_*,\qquad
 s_\varepsilon=(1-\varepsilon)s_*,\quad
 v_\varepsilon=(1-\varepsilon)v_*,\quad
 A_\varepsilon=\frac{a+v_\varepsilon}{1+s_\varepsilon},
 \qquad 0<\varepsilon<1.
\tag{206.34}
$$
式（206.9）为 $H_y=D_y-Q_y(s,v)$，其中
$D_y=(1-y)(y-a^2)>0$，$Q_y$ 为正定二次式。故
$$
 H_z(s_\varepsilon,v_\varepsilon)
 =D_z[1-(1-\varepsilon)^2]>0.
\tag{206.35}
$$
下端点在极限参数处已严格为正，缩放后仍严格为正。两个严格椭圆条件保证 $|A_\varepsilon|,|s_\varepsilon|<1$；定理204.2的实际处理器因此给出包含所需闭区间的精确开放延拓，且对全部信号输入成立。名义点在极限处满足
$H_h=\Delta k(\beta^2-\xi_*^2)>0$，所以满秩 SLD 成本连续收敛到（206.5）。

放大问题的最小值是原下确界的下界，这列实际程序给出反向不等式，故两者相等。唯一放大最小元也满足原非严格双端点条件，所以它是紧松弛的唯一最小元。原问题的不达到性沿用定理205.2；这里没有把上端点纯态误计为允许开放延拓的最优程序。证毕。

**定理 206.3（无剩余极小化的代数选择与严格资源曲线）。** 在定义206.1的条件下，令
$$
\begin{aligned}
 P_3(\xi)&=\sigma^2(\beta^2-\xi^2)
 -\xi(\alpha-\xi)(1-\alpha\xi),\\
 P_4(\xi)&=(1-\alpha\xi)(\beta^2-\xi^2)
 -\xi(\alpha-\xi)(1-\xi^2).
\end{aligned}
\tag{206.36}
$$
则 $\xi_*$ 也可唯一规定为
$$
\begin{gathered}
 (1-\xi^2)P_3(\xi)^2-a^2\sigma^2P_4(\xi)^2=0,\\
 0<\xi<\xi_b,\qquad P_3(\xi)<0<P_4(\xi).
\end{gathered}
\tag{206.37}
$$
该多项式的次数为八；条件（206.37）完整排除平方消根引入的其他分支。代入 $\xi=\alpha\lambda$ 后，其系数为 $a,h,z$ 的有理函数。

固定 $a,t$，成本 $R\mapsto\mathfrak M_2(a,t;R)$ 在全部合法超临界区间上实解析且导数严格为正。若记
$$
 R_{\max}=\min\{t-(2a-1),1-t\},\qquad
 L=\sup_{0<R<R_{\max}}\mathfrak M_2(a,t;R),
\tag{206.38}
$$
且 $R_0<R_{\max}$，则每个 $I_r(t)<C<L$ 对应唯一的
$R_C\in(R_0,R_{\max})$，满足 $\mathfrak M_2(a,t;R_C)=C$。在原问题中，存在名义信息成本不超过 $C$ 的实际程序，当且仅当
$$
 0<R<R_C.
\tag{206.39}
$$
因而预算给出的最大续接半径是未达到的上确界；$C\mapsto R_C$ 在这个区间实解析。

证明。 以 $r=\sqrt{1-\xi^2}$，将（206.3）中的双曲函数用（206.27）消去，得到未平方方程
$$
 rP_3(\xi)+a\sigma P_4(\xi)=0.
\tag{206.40}
$$
在一个解上，记 $D=\sigma r+a(1-\alpha\xi)>0$；直接代入驻点关系得
$$
 P_4(\xi)=\frac{\xi(\alpha-\xi)^3r}{\sigma D}>0,
 \qquad P_3(\xi)=-\frac{a\sigma}{r}P_4(\xi)<0.
\tag{206.41}
$$
平方（206.40）给出八次方程。反过来，规定的严格符号恢复（206.40），再恢复（206.3）；定理206.2保证唯一性。展开可见
$P_3=\sigma^2\beta^2-\alpha\xi+2\alpha^2\xi^2-\alpha\xi^3$，
$P_4=\beta^2-\alpha(\beta^2+1)\xi+2\alpha\xi^3-\xi^4$；代入 $\xi=\alpha\lambda$ 后只出现 $\alpha^2,\beta^2,\sigma^2$，证明有理系数断言。

各系数在合法超临界参数内解析，（206.32）给出非零根导数，所以隐函数定理使 $\xi_*$、$(A_*,s_*)$ 及其成本均实解析。为判成本导数的符号，使用（206.9）坐标下的放大问题。在 $H_z=0$ 上约束梯度不为零，因为它是正定椭圆的边界。其最小元的乘子满足
$$
 \nabla q_h=\lambda\nabla H_z,\qquad \lambda\ge0.
\tag{206.42}
$$
若 $\lambda=0$，便得到被超临界条件排除的内部驻点（206.12），故 $\lambda>0$。固定最优参数对时，由（206.16）得
$\partial_yH_y|_{y=z}=-(z-\ell_*)<0$。沿解析最优分支微分 $H_z=0$ 与目标函数，得到
$$
 \frac{d}{dR}\mathfrak M_2(a,t;R)
 =\frac\lambda2(z-\ell_*)>0.
\tag{206.43}
$$
这里 $q_h$ 自身不显含 $z$，而 $z=h+R/2$。因此每个紧超临界半径区间上，该资源曲线及其逆映射均为 Lipschitz。

在临界点右侧，定理203.2的二次起步给出成本趋于 $I_r(t)$；亚临界成本由定理201.3恒等于 $I_r(t)$。严格单调、连续性与上确界定义给出每个 $C\in(I_r,L)$ 的唯一 $R_C$；其导数非零保证逆函数解析。若 $R<R_C$，下确界严格小于 $C$，故存在成本小于 $C$ 的实际程序。若 $R>R_C$，任何程序成本均大于 $C$；在 $R=R_C$，定理205.2排除实际达到下确界 $C$。三种情形恰得（206.39）。证毕。

<a id="entry-762"></a>

## 追加锚（本行以下为增补区）

<a id="section-207"></a>

## 207. 全区间满秩程序的维数跃迁与固定三维的有限点校准

**定义 207.1（固定维数的全区间满秩成本）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$ 及整数 $d\ge1$。令 $\mathfrak F_d(a,t)$ 为以下程序的名义点态 SLD 信息量下确界：程序空间恰为 $\mathbb C^d$，一个固定 CPTP 处理器对所有信号输入、全部 $u\in J_a$ 精确产生 $\mathcal T_u$；程序曲线 $u\mapsto\rho_u$ 为 $C^\infty$，且在每个 $u\in J_a$ 都满足 $\rho_u\succ0$。空类的下确界定义为 $+\infty$。维数包括所有正交旗标，旗标的参数依赖信息也计入 SLD 成本。

**定理 207.2（满秩最优值的完整维数分类）。** 定义207.1的成本满足
$$
 \mathfrak F_d(a,t)=
 \begin{cases}
 +\infty,&d=1,\\
 \displaystyle\frac{1-a^2}{(1-t)(1+t-2a^2)},&d=2,\\
 \displaystyle\frac1{1-t^2},&d\ge3.
 \end{cases}
\tag{207.1}
$$
所有有限值均由实际满秩程序达到。对于 $d\ge3$，达到程序可以在左端 $u\downarrow2a-1$ 有满秩极限，并且在右端满足
$$
 \lambda_{\min}(\rho_u)=c(1-u)
\tag{207.2}
$$
对所有充分接近一的 $u$ 成立，其中 $c>0$。任何有限维的全区间精确程序都不可能在整个 $J_a$ 上具有一致正的最小特征值下界。

证明。 一维程序态恒为一，无法使固定处理器产生非恒定的通道族。二维下界和达到沿用定理190.2及第187节的满秩仿射构造。任意维数均受固定均衡 $02$ 读出的信息下界 $I_Q(\rho_t)\ge I_r(t)$ 约束。下面只构造 $d\ge3$ 的满秩达到；第190.3节已给出三维纯态达到，本节在相同维数增加全区间满秩实现。

置 $l=2a-1$，选取任意 $\zeta\in(l,t)$。取第200节在设计点 $\zeta$ 达到 $I_r(\zeta)$ 的最大物理区间二维程序，记为 $\sigma_v$、处理器为 $\mathcal G_2$，物理区间为 $(b_-,b_+)$。其显式形式也可从定义204.1取
$$
 A_\zeta=\frac{2a\zeta}{1+\zeta},\qquad s=0,\qquad
 \sigma_v=\frac12\left(I+
 \frac{2a-A_\zeta(1+v)}{\sqrt{1-A_\zeta^2}}X+vZ\right).
\tag{207.3}
$$
Bloch 正性给出整个 $(b_-,b_+)$ 上的满秩性；诱导通道恒等式在这个完整物理区间内仍为 $\mathcal T_v$。定理201.3证明
$$
 b_-<l<\zeta<b_+<1,
 \qquad I_Q(\sigma_\zeta)=\frac1{1-\zeta^2}.
\tag{207.4}
$$
内部程序坐标 $v$ 可以小于 $l$；（207.3）的正性与实际固定处理器保证该内部通道仍为 CPTP，不把 $J_a$ 的端点误当成完整 CP 边界。

选定 $v_c\in(b_-,l)$，并令
$$
 \nu=\frac{1-\zeta^2}{1-t^2},\qquad
 v_{\rm loc}(u)=\zeta+\nu(u-t).
\tag{207.5}
$$
因为 $b_-<\zeta<b_+$ 且 $\zeta<t$，存在 $t$ 的小开邻域 $V\Subset J_a$，使其中始终有
$b_-<v_{\rm loc}(u)<b_+$ 和 $v_{\rm loc}(u)<u$。取 $0\le\chi\le1$ 的光滑函数，支撑在 $V$ 内，且在 $t$ 的一个邻域恒为一。定义
$$
 v(u)=(1-\chi(u))v_c+\chi(u)v_{\rm loc}(u),\qquad
 w(u)=\frac{u-v(u)}{1-v(u)}.
\tag{207.6}
$$
在 $\chi(u)\ne0$ 处，两个参与插值的坐标都在物理区间内且小于当前 $u$；在其余位置只有常数 $v_c<l<u$。故在整个 $J_a$ 上
$$
 b_-<v(u)<b_+,\qquad v(u)<u<1,\qquad 0<w(u)<1.
\tag{207.7}
$$
这些函数为 $C^\infty$，并满足 $v(t)=\zeta$、$v'(t)=\nu$。

将程序空间取为 $\mathbb C^2\oplus\mathbb C^{d-2}$，准备
$$
 \rho_u=(1-w(u))\sigma_{v(u)}
 \oplus\frac{w(u)}{d-2}I_{d-2}.
\tag{207.8}
$$
第一块由 $\mathcal G_2$ 处理；第二块先对程序取迹，再对信号施行固定通道 $\mathcal T_1$；两个块之间的相干项由固定正交分区测量去除。压缩、部分迹和两个 CPTP 处理的和给出一个固定 CPTP 处理器，维数始终为 $d$。由于 $F(a,u)$ 关于 $u$ 仿射，
$$
 (1-w(u))\mathcal T_{v(u)}+w(u)\mathcal T_1
 =\mathcal T_{(1-w(u))v(u)+w(u)}
 =\mathcal T_u.
\tag{207.9}
$$
所以它对全部信号输入精确，并覆盖整个 $J_a$。由（207.7）和 $\sigma_v\succ0$，每个 $\rho_u$ 都满秩。

还须完整计入旗标的信息成本。若 $L_v$ 为 $\sigma_v$ 的 SLD，则（207.8）的 SLD 在两个块上分别为
$$
 -\frac{w'}{1-w}I_2+v'L_v,\qquad
 \frac{w'}w I_{d-2}.
\tag{207.10}
$$
由 $\operatorname{Tr}(\sigma_vL_v)=0$，平方取期望给出
$$
 I_Q(\rho_u)=\frac{w'(u)^2}{w(u)(1-w(u))}
 +(1-w(u))v'(u)^2I_Q(\sigma_{v(u)}).
\tag{207.11}
$$
第一项就是被计入的经典旗标 Fisher 信息。名义点处，由（207.5）—（207.6）得到
$$
 w(t)=\frac{t-\zeta}{1-\zeta},\qquad
 w'(t)=\frac{w(t)}{1+t},\qquad
 1-w(t)=\frac{1-t}{1-\zeta}.
\tag{207.12}
$$
代入（207.11）及（207.4），两项分别为
$$
 \frac{t-\zeta}{(1-t)(1+t)^2},\qquad
 \frac{1+\zeta}{(1-t)(1+t)^2}.
\tag{207.13}
$$
总和恰为 $1/(1-t^2)$。因此没有忽略旗标成本，也没有利用孤立秩变化处的 SLD 跳变，式（207.1）得证。

在 $J_a$ 的两个端点附近，$\chi=0$、$v=v_c$。左端的两个块权重都有严格正极限，故有满秩极限。右端则有
$$
 \rho_u=\frac{1-u}{1-v_c}\sigma_{v_c}
 \oplus\frac{u-v_c}{(1-v_c)(d-2)}I_{d-2}.
\tag{207.14}
$$
第二块的特征值趋于 $1/(d-2)>0$，第一块的特征值线性趋零，所以充分接近一时（207.2）成立，且
$c=\lambda_{\min}(\sigma_{v_c})/(1-v_c)>0$。

最后，对任意有限维固定处理器，均衡 $02$ 输入及相应二元输出读出在程序上诱导一个固定正效果 $E_-$，满足
$$
 \operatorname{Tr}(\rho_uE_-)=\frac{1-u}{2}.
\tag{207.15}
$$
它非零，因为右边在内部为正。由 $\rho_u\succeq\lambda_{\min}(\rho_u)I$ 得
$$
 \lambda_{\min}(\rho_u)
 \le\frac{1-u}{2\operatorname{Tr}E_-}.
\tag{207.16}
$$
故整个开放区间上的一致正下界不可能存在；构造（207.14）达到这个必需退化阶。在每个紧子区间，连续满秩性仍保证一致正下界。所有点态最优断言均针对预先指定的 $t$；不同设计点可选择不同处理器，不宣称同一个程序在整个区间处处达到 $I_r$。证毕。

**定理 207.3（任意有限校准集合只需同一满秩三维程序）。** 对任意有限非空集合 $S=\{t_1,\ldots,t_m\}\subset J_a$，存在一个固定 CPTP 处理器与一条 $C^\infty$ 三维程序曲线，在整个 $J_a$ 满秩、对全部信号输入精确生成 $\mathcal T_u$，并且
$$
 I_Q(\rho_{t_i})=I_r(t_i)\qquad(1\le i\le m).
\tag{207.17}
$$
它还可满足定理207.2的左端满秩极限与右端线性最小特征值。程序维数不随 $m$ 增长，并且三维是这种满秩有限校准的最小维数。此结论允许混合程序，与定理192.3的纯程序 $3m$ 维构造属于不同的秩约束。

证明。 取 $l<\zeta<\min S$，固定（207.3）的唯一一份种子程序及处理器，再取同一个 $v_c\in(b_-,l)$。对每个 $t_i$，置
$$
 v_i(u)=\zeta+\frac{1-\zeta^2}{1-t_i^2}(u-t_i).
\tag{207.18}
$$
选择两两不交的开邻域 $V_i\Subset J_a$，使其中 $b_-<v_i(u)<b_+$ 且 $v_i(u)<u$。选取支撑在 $V_i$ 的光滑函数 $0\le\chi_i\le1$，在 $t_i$ 附近恒为一，并定义
$$
 v(u)=\left(1-\sum_i\chi_i(u)\right)v_c
       +\sum_i\chi_i(u)v_i(u),\qquad
 w(u)=\frac{u-v(u)}{1-v(u)}.
\tag{207.19}
$$
任一点至多有一个 $\chi_i$ 非零；（207.7）的凸插值证明因此仍成立。取（207.8）的 $d=3$ 程序及同一个固定分块处理器，便在全部 $J_a$ 精确且满秩。每个 $t_i$ 处的值与一阶导数恰为（207.5）、（207.12）对应的数值，所以（207.11）—（207.13）逐点给出（207.17）。所有截断函数具有紧支撑，因此两端附近仍是（207.14）。定理190.2的二维下界严格大于 $I_r$，给出最小维数三。

此构造的等号条件还可精确区分有限校准与整段校准。令
$$
 h_\zeta=\frac{1+\zeta}{2},\qquad
 k=\frac{a^2}{h_\zeta^2-a^2\zeta^2},\qquad
 q(v)=1-v^2-k(1-\zeta v)^2.
\tag{207.20}
$$
由（207.3），种子 Bloch 向量为 $(\sqrt{k}(1-\zeta v),0,v)$，故满秩量子比特的 SLD 公式给出
$$
 E(v):=I_Q(\sigma_v)-I_r(v)
 =\frac{k(v-\zeta)^2}{(1-v^2)q(v)}.
\tag{207.21}
$$
把（207.11）展开、用 $w=(u-v)/(1-v)$ 消去旗标权重及其导数，有
$$
 I_Q(\rho_u)-I_r(u)
 =\frac{1-u}{1-v}v'^2E(v)
 +\frac{\big[(1-u^2)v'-(1-v^2)\big]^2}
 {(1-u^2)(1-v)^2(1+v)(u-v)}.
\tag{207.22}
$$
这里 $-1<v<u<1$、$q(v)>0$，两项非负。第二项为零迫使 $v'=(1-v^2)/(1-u^2)>0$，随后第一项为零等价于 $v=\zeta$。所以
$$
 I_Q(\rho_u)=I_r(u)
 \quad\Longleftrightarrow\quad
 v(u)=\zeta,\qquad
 v'(u)=\frac{1-\zeta^2}{1-u^2}.
\tag{207.23}
$$
每个等号点的导数严格为正，因而在它的某个邻域内只有一个 $v=\zeta$ 的点；等号点都是孤立的，不能把有限集合结论提升为一个开区间上的处处达到。

式（207.22）的第二项也说明旗标为什么不增加设计点的额外成本。把种子的均衡二元读出连同旗标保留，得到三项概率
$$
 \left((1-w)\frac{1+v}{2},\ (1-w)\frac{1-v}{2},\ w\right).
\tag{207.24}
$$
合并第一项与第三项后恰为 $((1+u)/2,(1-u)/2)$。在合并的正结果内部，旗标条件概率为 $\eta(u)=2w(u)/(1+u)$；经典 Fisher 链式分解给出被合并区分携带的信息为
$$
 \frac{1+u}{2}\frac{\eta'(u)^2}{\eta(u)(1-\eta(u))},
\tag{207.25}
$$
代入即为（207.22）的第二项。在设计点 $\eta'=0$；旗标本身的信息仍是（207.13）的正第一项，只是它与种子的正结果之间不再含额外的一阶信息。有限校准的构造没有免费旗标，也不由点态 SLD 等号推出全族的 CPTP 可恢复性。证毕。

固定处理器对混合程序态的线性作用见 Hillery、Ziman、Bužek，Phys. Rev. A **66**, 042302（2002），DOI:10.1103/PhysRevA.66.042302，第II.B节；包含经典混合信息的估计背景见 Alipour、Rezakhani，Phys. Rev. A **91**, 042104（2015），DOI:10.1103/PhysRevA.91.042104。这里使用固定正交块直接得到（207.11）的等式，再由本通道族的种子和光滑插值得到固定三维的精确校准。SLD 等号与可恢复性的差别见 Gao、Li、Marvian、Rouzé，arXiv:2302.02341v1，命题1.1与定理5.1；后者的正则 Fisher 度量条件不能替换成此处的点态 SLD 条件。

<a id="entry-764"></a>

## 追加锚（本行以下为增补区）

<a id="section-208"></a>

## 208. 有理满秩程序的精确校准集合与最小准备次数

**定义 208.1（固定种子混合坐标的有理次数）。** 固定 $0<a<1$、$l=2a-1$、种子点 $\zeta\in J_a$，以及（207.3）的二维种子 $\sigma_v$ 和物理区间 $(b_-,b_+)$。程序采用同一个固定处理器：二维块使用该种子处理器，一维旗标使用 $\mathcal T_1$。其准备曲线由实函数 $v$ 决定，
$$
 w(u)=\frac{u-v(u)}{1-v(u)},\qquad
 \rho_u=(1-w(u))\sigma_{v(u)}\oplus w(u).
\tag{208.1}
$$
要求 $v$ 在 $[l,1]$ 上有定义，且 $b_-<v(u)<b_+$、$v(u)<u$。因此 $\rho_u$ 在 $J_a$ 满秩、精确生成全部 $\mathcal T_u$。若 $v=N/D$ 是既约实有理函数且 $D$ 在 $[l,1]$ 无零点，定义其准备次数为
$$
 \deg_{\mathrm{prep}}(v)=\max\{\deg N,\deg D\}.
\tag{208.2}
$$
次数针对固定的物理参数 $u$ 与混合坐标 $v$，不是任意坐标变换下的不变量，也不定义所有量子程序的复杂度。

**定理 208.2（精确指定全部等号点的有理三维准备）。** 固定定义208.1的 $a,\zeta$ 及处理器。对任意有限非空集合
$$
 S=\{t_1<\cdots<t_m\}\subset(\zeta,1),
\tag{208.3}
$$
存在满足定义208.1的有理函数 $v$，并且
$$
 v(l)<\zeta,\qquad v(1)<\zeta,\qquad
 \{u\in J_a:I_Q(\rho_u)=I_r(u)\}=S.
\tag{208.4}
$$
可以令 $\deg_{\mathrm{prep}}(v)=2m$；在相同种子、混合方式及 $v(1)<\zeta$ 的端点约束下，任何至少在 $S$ 达到 $I_r$ 的有理准备都满足
$$
 \deg_{\mathrm{prep}}(v)\ge2m.
\tag{208.5}
$$
矩阵曲线 $\rho_u$ 在 $[l,1]$ 的一个实开邻域具有有理解析延拓，在左端仍满秩，在右端趋于旗标纯态，并满足
$$
 \lambda_{\min}(\rho_u)=c(1-u)+O((1-u)^2),\qquad c>0.
\tag{208.6}
$$
解析延拓不要求 $u>1$ 时仍为密度矩阵。固定处理器可在改变 $S$ 时保持不变；改变的是准备曲线。对下面的构造，旗标概率 $w$ 的既约分子、分母次数分别恰为 $2m+1$、$2m$。

证明。 选取 $v_c\in(b_-,l)$，令
$$
 P(u)=\prod_{i=1}^m(u-t_i),\quad
 s_i=\frac{1-\zeta^2}{1-t_i^2}>0,\quad
 L_i(u)=\frac{P(u)}{(u-t_i)P'(t_i)}.
\tag{208.7}
$$
这里 $L_i$ 是多项式，满足 $L_i(t_j)=\delta_{ij}$。采用一阶 Hermite 插值多项式
$$
 H(u)=\zeta+\sum_{i=1}^m s_i(u-t_i)L_i(u)^2.
\tag{208.8}
$$
它的次数不超过 $2m-1$，且 $H(t_i)=\zeta$、$H'(t_i)=s_i$。对 $\kappa>0$ 定义
$$
 D_\kappa(u)=1+\kappa P(u)^2,\qquad
 N_\kappa(u)=H(u)+\kappa v_cP(u)^2,\qquad
 v_\kappa(u)=\frac{N_\kappa(u)}{D_\kappa(u)}.
\tag{208.9}
$$
分母在实轴恒正。在每个 $t_i$，$P^2$ 及其一阶导数都为零，所以
$$
 v_\kappa(t_i)=\zeta,\qquad v_\kappa'(t_i)=s_i.
\tag{208.10}
$$

先验证全区间物理性。由 $b_-<\zeta<b_+$ 且 $\zeta<t_i$，可以选择各 $t_i$ 的两两不交小开邻域 $V_i\Subset(l,1)$，使其中 $b_-<H(u)<b_+$ 且 $H(u)<u$。在这些邻域内，（208.9）是 $H(u)$ 与 $v_c$ 的凸组合，故仍满足同样的三个严格不等式。紧集 $K=[l,1]\setminus\bigcup_iV_i$ 上 $P^2$ 有严格正下界；由
$$
 v_\kappa(u)-v_c=\frac{H(u)-v_c}{1+\kappa P(u)^2}
\tag{208.11}
$$
知 $v_\kappa\to v_c$ 在 $K$ 一致成立。常数 $v_c$ 到 $b_-,b_+$ 及所有 $u\in[l,1]$ 都有严格正余量。因此充分大的 $\kappa$ 使三个严格不等式在 $K$ 上也成立，并使 $v_\kappa(l),v_\kappa(1)<\zeta$。

一个只用插值系数和节点间距的充分选择如下。写 $H(u)=\sum_{j=0}^{2m-1}h_ju^j$，令
$$
 L=\sum_{j=1}^{2m-1}j|h_j|,\quad
 M=|h_0-v_c|+\sum_{j=1}^{2m-1}|h_j|,\quad
 \gamma=\min\{\zeta-b_-,b_+-\zeta,t_1-\zeta\}>0.
\tag{208.11a}
$$
取 $r>0$，满足
$$
 2r<\min\{t_1-l,1-t_m,\min_{i<m}(t_{i+1}-t_i)\},
 \qquad (L+1)r<\gamma/2,
\tag{208.11b}
$$
其中 $m=1$ 时省去节点间距项。再取
$$
 \delta=\tfrac12\min\{v_c-b_-,b_+-v_c,l-v_c\}>0,
 \qquad \kappa>\frac{M}{\delta r^{2m}}.
\tag{208.11c}
$$
由于 $[l,1]\subset[-1,1]$，$|H'|\le L$、$|H-v_c|\le M$。在 $|u-t_i|<r$ 内，$|H(u)-\zeta|\le Lr$ 给出所需物理余量及 $H(u)<u$；在其余位置，$P^2\ge r^{2m}$，故 $|v_\kappa-v_c|<\delta$，从而 $v_\kappa<l$ 并保留物理余量。该选择也使两端小于 $\zeta$。这只是一个充分界，不断言它优化了系数大小或数值条件。以下固定这样的 $\kappa$。

定义208.1的固定处理器和式（207.9）于是保证全部信号输入上的全区间精确性与内部满秩性。由（207.23）、（208.10），每个 $t_i$ 都达到 $I_r$。还须排除任何额外等号点，这不能只由插值条件推出。

置 $c_i=s_i/P'(t_i)^2>0$。在 $u\notin S$ 时，（208.8）给出
$$
 H(u)-\zeta=P(u)^2R(u),\qquad
 R(u)=\sum_{i=1}^m\frac{c_i}{u-t_i}.
\tag{208.12}
$$
故 $v_\kappa(u)=\zeta$ 的其余解恰满足
$$
 R(u)=\kappa(\zeta-v_c),\qquad
 R'(u)=-\sum_i\frac{c_i}{(u-t_i)^2}<0.
\tag{208.13}
$$
在每个 $(t_i,t_{i+1})$，$R$ 从正无穷严格降至负无穷，因此恰有一解 $r_i$；在 $(t_m,\infty)$，它从正无穷严格降至零，因此恰有一解 $r_m$；在 $(-\infty,t_1)$，它为负，没有解。由于 $v_\kappa(1)<\zeta$，最后一解满足 $r_m<1$。在这些额外根处，由
$$
 N_\kappa-\zeta D_\kappa
 =P^2\bigl[R-\kappa(\zeta-v_c)\bigr]
\tag{208.14}
$$
求导，得到 $v_\kappa'(r_i)=P(r_i)^2R'(r_i)/D_\kappa(r_i)<0$。这些根不满足（207.23）所需的正导数。所以等号集合恰为 $S$，而非只包含 $S$。

准备次数的上界直接来自（208.9）。其精确性也可由根结构核对：多项式 $N_\kappa-\zeta D_\kappa$ 次数为 $2m$，首项系数为 $\kappa(v_c-\zeta)\ne0$，并有刚证明的 $2m$ 个不同实根 $t_1,r_1,\ldots,t_m,r_m$。由于 $D_\kappa$ 没有实根，二者没有公共因子；因此 $N_\kappa,D_\kappa$ 已既约，次数恰为 $2m$。

再证（208.5）。对任何满足该结论前提的有理准备 $v=N/D$，在整个 $[l,1]$ 上将分母符号统一为正。由（207.23），$v(t_i)=\zeta$ 且 $v'(t_i)>0$，所以 $v-\zeta$ 在每个 $t_i$ 从负变正。每两个相邻的指定根之间，连续性迫使它另有一个根；$v(1)<\zeta$ 又迫使 $t_m$ 与一之间至少有一个根。于是非零多项式 $N-\zeta D$ 至少有 $2m$ 个不同实根，给出
$$
 2m\le\deg(N-\zeta D)\le\max\{\deg N,\deg D\}.
\tag{208.15}
$$
若移除右端的同侧条件，此论证只保证 $2m-1$ 个根，不能沿用（208.5）。

最后，$D_\kappa-N_\kappa=D_\kappa(1-v_\kappa)>0$ 在紧区间成立，因而（208.1）各矩阵元都是在其邻域无实极点的有理函数。左端 $v(l)<l$ 与内部物理性给出两个块的正权重和满秩性。右端写 $v_1=v(1)$，则
$$
 (1-w(u))\sigma_{v(u)}
 =\frac{1-u}{1-v_1}\sigma_{v_1}+O((1-u)^2),\qquad
 w(u)\longrightarrow1.
\tag{208.16}
$$
Hermitian 矩阵的最小特征值关于算子范数为 Lipschitz，且 $\sigma_{v_1}\succ0$，故（208.6）成立，其中 $c=\lambda_{\min}(\sigma_{v_1})/(1-v_1)>0$。这也与（207.16）的普遍上界相容。

旗标概率本身为
$$
 w(u)=\frac{uD_\kappa(u)-N_\kappa(u)}{D_\kappa(u)-N_\kappa(u)}.
\tag{208.17}
$$
分子、分母次数分别为 $2m+1$、$2m$。任何公共因子也须整除 $(u-1)D_\kappa$ 与 $D_\kappa-N_\kappa$；前述既约性排除来自 $D_\kappa$ 的因子，而 $D_\kappa(1)-N_\kappa(1)>0$ 排除 $u-1$，所以没有约分。这个次数结论描述实际旗标准备概率；它不提供门数、系数位数或其他准备架构的普遍下界。证毕。

Hermite 插值与有理形状约束的背景可见 Gregory、Delbourgo，*Piecewise Rational Quadratic Interpolation to Monotonic Data*，IMA J. Numer. Anal. **2**（1982），123–130，第2节式（2.2）—（2.7）。该文的分段单调约束在相同函数值处要求零端点导数；本节所有指定节点具有相同值及正导数，其间必须出现回程。这里由（208.12）—（208.14）确定这些回程，并验证它们与固定量子处理器的物理约束及精确 Fisher 等号集合相容。

<a id="entry-766"></a>

## 追加锚（本行以下为增补区）

<a id="section-209"></a>

## 209. 仿射准备的维数无关信息缺口与三维严格改进

**定义 209.1（维数受限的仿射程序成本）。** 固定 $0<a<1$、$l=2a-1$、$t\in J_a=(l,1)$ 及整数 $d\ge1$。令 $\mathfrak A_d(a,t)$ 为所有下列程序的名义点态 SLD 信息量下确界：程序的联合支持维数不超过 $d$，状态在物理参数 $u$ 中仿射，$\rho_u=M+uN$；一个不依赖 $u$ 的 CPTP 处理器对全部信号输入、全部 $u\in J_a$ 精确产生 $\mathcal T_u$。允许把较小支持嵌入 $\mathbb C^d$，不要求程序在填充后的整个空间满秩；空类的下确界为 $+\infty$。

**定理 209.2（仿射准备具有维数无关的正额外成本）。** 任意有限维全区间精确仿射程序都满足
$$
 I_Q(\rho_t)\ge I_r(t)+
 \frac{a^2}{4(1+t)^2}>I_r(t),
 \qquad I_r(t)=\frac1{1-t^2}.
\tag{209.1}
$$
此外 $\mathfrak A_1(a,t)=+\infty$；对于每个有限 $d\ge2$，定义209.1的下确界被实际程序达到，且
$$
 I_r(t)+\frac{a^2}{4(1+t)^2}
 \le\mathfrak A_d(a,t)
 \le B(a,t)=\frac{1-a^2}{(1-t)(1+t-2a^2)}.
\tag{209.2}
$$
其中 $\mathfrak A_2=B$，$\mathfrak A_{d+1}\le\mathfrak A_d$。维数增加不能使仿射程序成本趋于 $I_r$；这里不宣称（209.1）的附加项是最优常数。

证明。 先处理支持与秩。若 $x\in\ker\rho_t$，则 $\langle x,\rho_u x\rangle=(u-t)\langle x,Nx\rangle$ 在 $t$ 的两侧非负，故 $\langle x,Nx\rangle=0$。该二次型在整个区间为零；由 $\rho_u\succeq0$，有 $\rho_u x=0$。交换两个内部参数可知各内点的核相同。因此仿射程序在共同支持上满秩，导数在其正交补消失，内部 SLD 信息量有限。这一步不要求端点具有相同支持。

先从处理器的全输入约束提取一个算子关系。限制到原程序的共同支持；其内部态满秩。对每个信号基态 $|i\rangle$，输出恒为纯态 $|i\rangle\langle i|$。把一个内部程序态分解为正权本征投影，输出在其正交补的非负概率之和为零，故 Stinespring 等距必在整个共同支持上具有受控形状
$V=\sum_{i=0}^2|i\rangle\langle i|\otimes V_i$，其中 $V_i^\dagger V_i=I$。这个形状由精确性推出，不是额外架构限制。

依照第204节，将处理器与同时交换信号输入、输出标号 $0,2$ 后的处理器平均。目标通道对此交换不变，程序曲线和成本也不变。平均后的算子 Gram 矩阵可写成
$$
 \mathsf G=\begin{pmatrix}
 I&K&A\\K^\dagger&I&K^\dagger\\A&K&I
 \end{pmatrix}\succeq0,\qquad A=A^\dagger,
 \qquad \operatorname{Tr}(\rho_uA)=u,\quad
 \operatorname{Tr}(\rho_uK)=a.
\tag{209.3}
$$
这里可以取 $A=(V_0^\dagger V_2+V_2^\dagger V_0)/2$、$K=(V_0^\dagger V_1+V_2^\dagger V_1)/2$。在外侧的对称、反对称坐标中对（209.3）作 Schur 补，得到
$$
 -I\preceq A\preceq I,\qquad
 KK^\dagger\preceq E_+:=\frac{I+A}{2},\qquad
 E_-:=\frac{I-A}{2},\qquad K=\sqrt{E_+}\,C,
 \quad \|C\|_\infty\le1.
\tag{209.4}
$$
最后的分解可在 $E_+$ 的支持上取逆平方根直接构造；不等式保证 $K$ 的像包含于该支持，且 $CC^\dagger\preceq I$。

使用固定等距嵌入 $Jx=\sqrt{E_+}x\oplus\sqrt{E_-}x$，记两个直和投影为 $P,Q$、第一块嵌入为 $\iota_+$。令
$$
 \sigma_u=J\rho_uJ^\dagger,\qquad
 \widetilde K=\iota_+CJ^\dagger.
 \quad
 P\widetilde K=\widetilde K,\qquad
 \|\widetilde K\|_\infty\le1,\qquad
 \operatorname{Tr}(\sigma_u\widetilde K)=a.
\tag{209.5}
$$
这是因为 $J^\dagger\widetilde KJ=\sqrt{E_+}C=K$。此外
$\operatorname{Tr}(P\sigma_u)=(1+u)/2$、$\operatorname{Tr}(Q\sigma_u)=(1-u)/2$。
嵌入曲线仍仿射，SLD 信息量在固定等距下保持。这里只在扩大空间使用这些算子关系，不要求扩大空间上的任意态产生预先指定的信号通道。

在名义点记 $N_\sigma=\sigma'_t$，取一个满足 SLD 方程的自伴 $L_t$，并置
$$
 H_t=\frac{P}{1+t}-\frac{Q}{1-t},\qquad
 R_t=N_\sigma-\frac12(H_t\sigma_t+\sigma_tH_t),\qquad
 g=I_Q(\sigma_t)-I_r(t).
\tag{209.6}
$$
概率与导数恒等式给出
$\operatorname{Tr}(N_\sigma H_t)=\operatorname{Tr}(\sigma_tH_t^2)=I_r(t)$。
因此第189节的得分残差恒等式在这里成为
$$
 g=\operatorname{Tr}[\sigma_t(L_t-H_t)^2],\qquad
 R_t=\tfrac12[(L_t-H_t)\sigma_t+\sigma_t(L_t-H_t)],
 \qquad \|R_t\|_1\le\sqrt g.
\tag{209.7}
$$
最后一步由 Schatten Cauchy–Schwarz 与 $\operatorname{Tr}\sigma_t=1$ 得到；公式不要求嵌入态在整个扩大空间可逆，所以也覆盖秩亏程序。

仿射曲线在 $u\uparrow1$ 有密度矩阵极限 $\sigma_1$。由于 $\operatorname{Tr}(\sigma_1Q)=0$，正性迫使 $Q\sigma_1=\sigma_1Q=0$。按照 $P\oplus Q$ 分块，写
$$
 \sigma_t=\begin{pmatrix}A_0&C_0\\C_0^\dagger&B_0\end{pmatrix}.
\tag{209.8}
$$
整个曲线的仿射性给出
$$
 (N_\sigma)_{QQ}=-\frac{B_0}{1-t},\qquad
 (N_\sigma)_{PQ}=-\frac{C_0}{1-t},\qquad
 (R_t)_{QQ}=0,\qquad
 (R_t)_{PQ}=-\frac{C_0}{1-t^2}.
\tag{209.9}
$$
取实际密度矩阵
$$
 \tau=\frac{2Q\sigma_tQ}{1-t},\qquad Z_0=P-Q.
\tag{209.10}
$$
其迹为一。用 $\sigma_{-1}=\sigma_t-(1+t)N_\sigma$ 表示仿射公式的代数延伸；此时不要求 $\sigma_{-1}$ 正定或半正定。由（209.9）以及
$(R_t)_{PP}=(N_\sigma)_{PP}-A_0/(1+t)$，逐块得到
$$
 \sigma_{-1}-\tau
 =-(1+t)\left(\frac32R_t-\frac12Z_0R_tZ_0\right).
\tag{209.11}
$$
$Z_0$ 为酉自伴算子，故
$$
 \|\sigma_{-1}-\tau\|_1\le2(1+t)\sqrt g.
\tag{209.12}
$$

恒等式 $\operatorname{Tr}(\sigma_u\widetilde K)=a$ 关于 $u$ 仿射，因而在代数延伸 $u=-1$ 处仍成立。另一方面，$\tau$ 支持于 $Q$，而 $P\widetilde K=\widetilde K$，所以 $\operatorname{Tr}(\tau\widetilde K)=0$。于是
$$
 a=\big|\operatorname{Tr}[(\sigma_{-1}-\tau)\widetilde K]\big|
 \le\|\sigma_{-1}-\tau\|_1\le2(1+t)\sqrt g.
\tag{209.13}
$$
这证明（209.1），其中迹范数没有除以二。全输入约束在这里通过（209.3）—（209.5）的常数通道系数参与估计，不能只用二元概率关系替代。

下面固定维数上界 $d$。任何仿射程序都有密度矩阵端点 $\tau_l,\tau_1$，且
$$
 \rho_u=\frac{1-u}{1-l}\tau_l+
         \frac{u-l}{1-l}\tau_1,
 \qquad N=\frac{\tau_1-\tau_l}{1-l}.
\tag{209.14}
$$
把所有程序填充到 $\mathbb C^d$，以两个端点态及处理器的 Choi 矩阵作为参数。密度矩阵集合与固定输入、输出维数的 CPTP Choi 集合都紧。要求处理器在两个端点对每个信号矩阵单位给出目标通道，是有限个连续等式，所以可行集闭且紧。端点约束由连续性从原程序得到；反向由（209.14）与目标通道的仿射性保证整个区间精确。

名义点的 SLD 信息量具有变分式
$$
 I_Q(\rho_t,N)=
 \sup_{H=H^\dagger}
 \{2\operatorname{Tr}(NH)-\operatorname{Tr}(\rho_tH^2)\}.
\tag{209.15}
$$
在共同支持上取 SLD $L$ 并完成平方，花括号等于
$I_Q(\rho_t)-\operatorname{Tr}[\rho_t(H-L)^2]$，上确界在 $H=L$ 达到；核外部分不改变上确界。每个固定 $H$ 的表达式关于参数连续，故信息量为下半连续函数，紧可行集上的下确界被达到。这里允许极限的支持维数下降，不对满秩态开集使用紧性。

第187节的全区间仿射二维程序达到 $B(a,t)$。填充程序并对额外块选任意固定通道可延拓处理器，所以 $d\ge2$ 时可行集非空且最小值有限。（209.1）给出下界；一维程序不能生成非恒定通道族；定理190.2给出 $\mathfrak A_2=B$；填充关系给出随维数不增。证毕。

**定理 209.3（三维仿射程序严格优于二维最优值）。** 对 $a=t=1/2$，存在一个在整个 $J_a=(0,1)$ 满秩、对全部信号输入精确的三维仿射程序，满足
$$
 I_Q(\rho_{1/2})=
 \frac{320811687543628211492}{214265320278484424375}
 <\frac32=B(1/2,1/2).
\tag{209.16}
$$
因此 $\mathfrak A_3(1/2,1/2)<\mathfrak A_2(1/2,1/2)$。本式给出严格改进，不断言该三维程序已经最优。

证明。 取
$$
 K=\frac1{100}\begin{pmatrix}
 72&20&-64\\-55&37&-61\\0&0&0
 \end{pmatrix},\qquad Z=\operatorname{diag}(1,1,-1),
\tag{209.17}
$$
以及两个端点
$$
 R=\begin{pmatrix}
 41/100&19/100&-1/4\\
 19/100&9/100&-39/305\\
 -1/4&-39/305&1/2
 \end{pmatrix},\qquad
 S=\begin{pmatrix}
 39/50&143/350&0\\
 143/350&11/50&0\\
 0&0&0
 \end{pmatrix}.
\tag{209.18}
$$
$R$ 的顺序主子式为 $41/100,1/1250,1303/5953600$；$S$ 的非零二阶块的顺序主子式为 $39/50,143/30625$。两矩阵的迹均为一，所以 $R\succ0$、$S\succeq0$，且
$$
 \rho_u=(1-u)R+uS\succ0\qquad(0<u<1).
\tag{209.19}
$$
$I-KK^\dagger$ 的上二阶块顺序主子式为 $4/125,8459/6250000$，其余块为一，故 $K$ 是严格压缩算子。定义固定等距映射
$$
 W_0=\binom{I_3}{0},\qquad
 W_2=\binom{Z}{0},\qquad
 W_1=\binom{K}{\sqrt{I_3-K^\dagger K}}.
\tag{209.20}
$$
受控等距 $V=\sum_{i=0}^2|i\rangle\langle i|\otimes W_i$ 后取环境偏迹，给出固定 CPTP 处理器。直接相乘有
$$
 ZK=K,\qquad
 \operatorname{Tr}(RK)=\operatorname{Tr}(SK)=\tfrac12,
 \qquad \operatorname{Tr}(RZ)=0,
 \quad \operatorname{Tr}(SZ)=1.
\tag{209.21}
$$
因此诱导 Schur 系数为 $C_{01}=C_{12}=1/2$、$C_{02}=u$、$C_{ii}=1$，并由自伴性确定其他项。这逐矩阵单位证明全部信号输入上的恒等式，精确域是整个 $(0,1)$。

在名义点令 $\rho=(R+S)/2$、$N=S-R$。由于 $\rho\succ0$，实对称线性方程
$$
 \tfrac12(\rho L+L\rho)=N
\tag{209.22}
$$
有唯一实对称解。将（209.18）代入这组六元线性方程并消元，得到
$\operatorname{Tr}(NL)=\operatorname{Tr}(\rho L^2)$ 等于（209.16）的有理数。严格差为
$$
 \frac32-I_Q(\rho_{1/2})
 =\frac{1172585748196850141}{428530640556968848750}>0.
\tag{209.23}
$$
由此，二维下界 $B$ 不能作为所有仿射程序的通用下界；它与（209.1）的维数无关正差距相容。证毕。

固定混合程序的线性框架与得分残差沿用第187—189节。混合态的 SLD 公式及量子比特、纯端点特化可参见 de Vicente 等，*Estimation of quantum finite mixtures*，arXiv:0910.1525v2，式（82）—（86）；纯端点混合的成本公式不适用于（209.18）的两个混合端点。这里的维数无关下界使用全区间仿射性与端点正性，三维改进使用显式处理器与上述矩阵。两者共同说明：增加维数可以降低仿射成本，但第207节的三维零额外成本还需要非仿射准备。

<a id="entry-768"></a>

## 追加锚（本行以下为增补区）

<a id="section-210"></a>

## 210. 一阶光滑量子程序的有限校准与 Lipschitz 端点聚集

**定义 210.1（校准集合与光滑端点）。** 固定 $0<a<1$、$l=2a-1$，沿用第187节的有限维固定程序：同一个 CPTP 处理器以程序态 $\rho_u$ 对所有信号输入精确产生 $\mathcal T_u$，参数域为 $J_a=(l,1)$。令
$$
 \mathcal E(\rho)=\{u\in J_a:I_Q(\rho_u)=I_r(u)\},
 \qquad I_r(u)=\frac1{1-u^2}.
\tag{210.1}
$$
$I_Q$ 使用点态 SLD 约定，不在秩变化点改用其连续延拓。称程序具有一阶光滑端点，是指其矩阵元素具有包含闭区间 $[l,1]$ 的实开邻域上的 $C^1$ 延拓；只要求延拓在物理参数域内为密度矩阵。允许程序秩随参数变化。

**定理 210.2（一阶光滑程序的孤立校准与局部二次下界）。** 设 $\rho_u$ 在 $J_a$ 上为 $C^1$ 曲线。按第188.3节对固定均衡 $02$ 读出作 Naimark 嵌入，记 $\sigma_u=J\rho_uJ^\dagger$、互补投影为 $P,Q$，并定义
$$
 h(u)=\frac{1+u}{2},\quad e(u)=\frac{1-u}{2},\quad
 K_u=\sqrt{h(u)}P+\sqrt{e(u)}Q,\quad
 H_u=\frac{P}{1+u}-\frac{Q}{1-u},
 \qquad R_u=\sigma'_u-\frac12(H_u\sigma_u+\sigma_uH_u).
\tag{210.2}
$$
令 $\Phi$ 为经第188.3节固定 CPTP 解码扩张后的处理器所诱导的线性映射：它把扩大空间上的程序矩阵送到相应的信号线性映射。则 $\mathcal B(u):=\Phi(R_u)$ 为 $C^1$ 函数，并且每个 $t\in\mathcal E(\rho)$ 都满足
$$
 R_t=0,\qquad \mathcal B(t)=0,\qquad \mathcal B'(t)\ne0.
\tag{210.3}
$$
因此存在依赖该程序与 $t$ 的 $c,\delta>0$，使
$$
 I_Q(\rho_u)-I_r(u)\ge c|u-t|^2
 \qquad(|u-t|<\delta).
\tag{210.4}
$$
若曲线为 $C^2$，则另有 $R'_t\ne0$；若同时在 $t$ 的一个邻域秩恒定，则存在有限常数 $C$，使同一信息差值至多为 $C|u-t|^2$。不要求该恒秩支持子空间本身固定。

证明。 固定嵌入及 CPTP 解码扩张使 $\Phi$ 对扩大空间上的所有程序矩阵都有定义；密度矩阵经 $\Phi$ 给出 CPTP 通道，且 $\Phi(\sigma_u)=\mathcal T_u$。后面构造的密度矩阵不必位于原嵌入像中。

对任何内点，双侧正性给出 $\sigma'_u$ 在 $\ker\sigma_u$ 上的压缩为零，因此有限自伴 SLD $L_u$ 存在。第189节的平方残差恒等式给出
$$
 g(u):=I_Q(\rho_u)-I_r(u)
 =\operatorname{Tr}[\sigma_u(L_u-H_u)^2],
 \qquad \|R_u\|_1\le\sqrt{g(u)}.
\tag{210.5}
$$
若 $g(u)=0$，则 $(L_u-H_u)\sqrt{\sigma_u}=0$，故 $R_u=0$。反过来，若 $R_u=0$，则 $H_u$ 本身满足 SLD 方程，而且
$\operatorname{Tr}(\sigma_uH_u^2)=1/(1-u^2)$，故 $g(u)=0$。这证明等号与 $R_u=0$ 等价，没有对态、SLD 或信息量的可逆性和解析性作假设。

记 $\mathcal M_u(X)=(H_uX+XH_u)/2$。目标通道仿射，全输入精确恒等式给出
$$
 \mathcal B(u)=\Phi(R_u)
 =\mathcal T'-\Phi(\mathcal M_u(\sigma_u)).
\tag{210.6}
$$
右侧只含 $C^1$ 函数 $\sigma_u$ 及光滑算子 $\mathcal M_u$，所以 $\mathcal B$ 为 $C^1$；这一步不要求 $R$ 可微。

固定校准点 $t$，置正矩阵 $A=K_t^{-1}\sigma_tK_t^{-1}$，记
$A_+=PAP$、$A_-=QAQ$、$D=PAQ$。读出概率为 $h,e$，所以 $A_+$ 和 $A_-$ 都有迹一。定义固定通道 $\mathcal R_\pm=\Phi(A_\pm)$ 及固定线性映射 $\mathcal S=\Phi(D+D^\dagger)$。冻结曲线 $\widehat\sigma_u=K_uAK_u$ 的通道为
$$
 \Psi_u=h(u)\mathcal R_++e(u)\mathcal R_-
       +q(u)\mathcal S,
 \qquad q(u)=\frac12\sqrt{1-u^2}.
\tag{210.7}
$$
由于 $K'_u=H_uK_u/2$，冻结曲线满足 $\widehat\sigma'_u=\mathcal M_u(\widehat\sigma_u)$。在 $t$，$R_t=0$ 保证冻结曲线与实际曲线有相同的值及一阶导数。因此对（210.6）求导，只使用实际曲线的一阶导数便有
$$
 \mathcal B'(t)
 =-\Phi(\mathcal M'_t(\sigma_t)+\mathcal M_t(\sigma'_t))
 =-\Psi''_t=-q''(t)\mathcal S,
 \qquad q''(t)=-\frac1{2(1-t^2)^{3/2}}\ne0.
\tag{210.8}
$$
若 $\mathcal B'(t)=0$，则 $\mathcal S=0$。再匹配冻结曲线与目标通道的值、一阶导数，得到
$$
 \mathcal R_-=\mathcal T_t-(1+t)\mathcal T'=\mathcal T_{-1}.
\tag{210.9}
$$
左侧是 CPTP 通道，右侧却不为正：第188.3节的 $n=(1,-2a,1)^{\mathsf T}$ 满足 $n^{\mathsf T}F(a,-1)n=-4a^2$。矛盾证明（210.3）。

在有限维信号映射空间任选一个范数，取 $M>0$ 使 $\|\Phi(X)\|\le M\|X\|_1$ 对所有自伴 $X$ 成立。由 $\mathcal B(t)=0$、$\mathcal B'(t)\ne0$，在充分小的邻域有
$\|\mathcal B(u)\|\ge\frac12\|\mathcal B'(t)\||u-t|$。结合（210.5）得到（210.4），例如可取 $c=\|\mathcal B'(t)\|^2/(4M^2)$。因此校准点孤立，即使残差本身只有连续性。

若 $\rho$ 为 $C^2$，则 $R$ 为 $C^1$ 且 $\mathcal B'(t)=\Phi(R'_t)\ne0$，所以 $R'_t\ne0$。若秩还局部恒定，所有非零特征值在缩小的邻域具有统一正下界 $\lambda_*>0$。在 $\sigma_u$ 的本征基中，以 $\lambda_i$ 表示特征值，有
$$
 g(u)=2\sum_{\lambda_i+\lambda_j>0}
       \frac{|(R_u)_{ij}|^2}{\lambda_i+\lambda_j}
 \le\frac2{\lambda_*}\|R_u\|_2^2.
\tag{210.10}
$$
这是把 $(R_u)_{ij}=(\lambda_i+\lambda_j)(L_u-H_u)_{ij}/2$ 代入平方残差后对有序指标对求和所得；核与核之间的项不贡献，支持与核之间的项仍保留。$R_t=0$ 与 $C^1$ 性给出所需二次上界。秩变化时这个统一分母下界不成立；第188.4节的程序在校准点外具有严格正的信息量极限差，不能把上界推广到所有秩变化点。证毕。

**定理 210.3（光滑端点下的全部校准集合恰为有限集合）。** 每个具有定义210.1所述一阶光滑端点的有限维全区间精确程序，其 $\mathcal E(\rho)$ 都是有限集合。反过来，$J_a$ 的每个有限子集，包括空集，都可以成为一个三维程序的完整校准集合；实现程序在 $J_a$ 内满秩，其矩阵元素在 $[l,1]$ 附近有有理解析延拓。非空集合的最小程序维数为三。即使维数固定为三，各程序校准点数也不存在统一有限上界。

证明。 若等号点无限，则在紧区间 $[l,1]$ 上有聚点。内点聚集由 $R$ 的连续性给出 $R_t=0$，而相应的 $\mathcal B$ 零点序列迫使 $\mathcal B(t)=\mathcal B'(t)=0$，与定理210.2矛盾。若聚点为 $l$，由于 $l>-1$，$K_l$ 仍可逆。连续性给出 $\sigma_l\succeq0$、读出概率恒等式及 $R_l=0$；处理器像仍具有（210.6）的 $C^1$ 表达，零点聚集给出 $\mathcal B'(l)=0$。定理210.2对冻结曲线及处理器像的导数论证可在 $l$ 应用，仍得到不为正的 $\mathcal T_{-1}$ 必须为 CPTP，矛盾。此处只对实际曲线使用物理侧的一阶导数极限，不要求延拓在 $u<l$ 时保持正性。

在右端，令 $Z=P-Q$，消去 $H$ 的分母，定义
$$
 T(u)=(1-u^2)R_u
      =(1-u^2)\sigma'_u+u\sigma_u
       -\frac12(Z\sigma_u+\sigma_uZ).
\tag{210.11}
$$
由 $\operatorname{Tr}(Q\sigma_1)=0$ 与正性，有 $Q\sigma_1=\sigma_1Q=0$，故 $T(1)=0$。一阶光滑性给出 $\sigma_u=\sigma_1+(u-1)\sigma'_1+o(|u-1|)$ 及 $\sigma'_u=\sigma'_1+o(1)$，所以即使 $\sigma''_1$ 不存在，$T$ 仍有左导数 $T'(1)=\sigma_1-\sigma'_1-(Z\sigma'_1+\sigma'_1Z)/2$。若等号点趋于一，则这个导数必须为零。按 $P,Q$ 分块计算，得到
$$
 P\sigma'_1P=\frac12\sigma_1,
 \qquad P\sigma'_1Q=Q\sigma'_1P=0.
\tag{210.12}
$$
从 $u<1$ 一侧的 $Q\sigma_uQ\succeq0$ 得 $Q\sigma'_1Q\preceq0$。而读出概率的导数为 $\operatorname{Tr}(Q\sigma'_1)=-1/2$，所以
$$
 \tau_-=-2Q\sigma'_1Q\succeq0,\qquad
 \operatorname{Tr}\tau_-=1,\qquad
 \sigma'_1=\frac12(\sigma_1-\tau_-).
\tag{210.13}
$$
送入固定处理器得到
$\Phi(\tau_-)=\mathcal T_1-2\mathcal T'_1=\mathcal T_{-1}$，再次与正性矛盾。因此两端也不能成为聚点，校准集合有限。

对于非空有限集合 $S\subset J_a$，选 $\zeta\in(l,\min S)$，直接使用定理208.2的有理准备，便有 $\mathcal E(\rho)=S$。其处理器固定于所选种子；同一处理器可以服务 $(\zeta,1)$ 内的任意有限集合。对于空集，在第207节的种子加旗标构造中取恒定 $v(u)=v_c\in(b_-,l)$；整个闭区间上 $v_c<u$，准备保持物理性，内部满秩，且式（207.23）的正导数条件处处不成立。相应旗标权重 $w=(u-v_c)/(1-v_c)$ 与矩阵曲线均在端点附近解析。第190.2节的二维成本严格大于 $I_r$，排除非空集合的二维实现；三维实现给出反向达到。取任意大的有限 $|S|$，说明维数三本身不限制校准点数。证毕。

**定理 210.4（仅有开区间解析性时可以有无穷多个校准点）。** 固定第207节的任意种子 $\zeta\in J_a$ 及其物理区间 $(b_-,b_+)$。选择
$$
 b_-<c<l<\zeta<d<b_+,
 \qquad
 g(y)=c+\frac{d-c}{1+C e^{-ky}},
 \quad C=\frac{d-\zeta}{\zeta-c},
 \quad k=\frac{(1-\zeta^2)(d-c)}{(\zeta-c)(d-\zeta)}.
\tag{210.14}
$$
对充分大的实数 $\beta$，令
$$
 x=\operatorname{artanh}u,\qquad
 \theta_\beta(x)=-\frac\pi2+\log(1+e^{x-\beta}),\qquad
 r_\beta(x)=\theta'_\beta(x)=\frac{e^{x-\beta}}{1+e^{x-\beta}},
 \qquad
 v_\beta(u)=g\!\left(\frac{\sin\theta_\beta(x)}{r_\beta(x)}\right).
\tag{210.15}
$$
使用同一个种子加旗标处理器，存在以此内部坐标准备的全区间精确三维程序，在 $J_a$ 内满秩且实解析，其完整校准集合恰为
$$
 \mathcal E(\rho)=
 \left\{\tanh\!\left[\beta+
 \log\!\left(e^{\pi/2+2\pi n}-1\right)\right]:n=0,1,2,\ldots\right\}.
\tag{210.16}
$$
这些点递增趋于一。程序在左端具有解析延拓，在右端连续趋于旗标纯态；闭区间上的连续延拓为 Lipschitz 函数，但在右端没有 $C^1$ 延拓。

证明。 函数 $g$ 严格递增，值域为 $(c,d)$，且 $g(0)=\zeta$、$g'(0)=1-\zeta^2$。所有组成函数在 $J_a$ 上解析，$r_\beta>0$，故 $v_\beta$ 解析并始终位于种子的物理区间内。

当 $\beta\to+\infty$，在紧区间 $u\in[l,d]$ 上有 $r_\beta\to0$、$\theta_\beta\to-\pi/2$，且 $\sin\theta_\beta/r_\beta\to-\infty$ 一致成立。因此 $v_\beta\to c<l$ 一致成立。固定充分大的 $\beta$，使该区间上 $v_\beta<l$，并且 $\theta_\beta(\operatorname{artanh}d)<0$。对于 $u>d$，自动有 $v_\beta<d<u$；故整个 $J_a$ 上 $v_\beta<u$。取
$$
 w_\beta(u)=\frac{u-v_\beta(u)}{1-v_\beta(u)},\qquad
 \rho_u=(1-w_\beta(u))\sigma_{v_\beta(u)}\oplus w_\beta(u).
\tag{210.17}
$$
两块权重严格为正，种子态满秩；同一个固定处理器给出 $(1-w_\beta)\mathcal T_{v_\beta}+w_\beta\mathcal T_1=\mathcal T_u$。这证明全区间、全输入的精确性与三维满秩性。

由 $g$ 的单射性，$v_\beta=\zeta$ 当且仅当 $\sin\theta_\beta=0$。在这些点，直接求导得到
$$
 \frac{dv_\beta}{dx}=(1-\zeta^2)\cos\theta_\beta,
 \qquad
 \frac{dv_\beta}{du}=\frac{1-\zeta^2}{1-u^2}\cos\theta_\beta.
\tag{210.18}
$$
式（207.23）因而恰好选择 $\theta_\beta=2\pi n$。由于 $\theta_\beta$ 严格递增、在 $\operatorname{artanh}l$ 的值位于 $(-\pi/2,0)$，且趋于正无穷，允许的整数恰为 $n\ge0$。解出 $u$ 得（210.16）；第一点已在 $d$ 右侧。

左端 $l\in(-1,1)$，且构造的分母在那里非零，所以左侧矩阵解析延拓存在。在右端，$v_\beta\in(c,d)$ 一致远离一，故活动量子比特块的迹为 $(1-u)/(1-v_\beta(u))\to0$，程序连续趋于旗标纯态。若右端存在左导数，该块迹除以 $1-u$ 应有极限。但沿（210.16）的序列，它恒为 $1/(1-\zeta)$；沿 $\theta_\beta=\pi/2+2\pi n$ 的序列，$r_\beta\to1$、$v_\beta\to g(1)>\zeta$，故该商趋于不同的数 $1/(1-g(1))$。右端导数不存在，因而不与定理210.3矛盾。

还可直接验证整个闭区间上的 Lipschitz 性。令 $y=\sin\theta_\beta/r_\beta$，利用 $\partial_xr_\beta=r_\beta(1-r_\beta)$ 得
$$
 \partial_xy=\cos\theta_\beta-
       \frac{1-r_\beta}{r_\beta}\sin\theta_\beta.
$$
对于固定的 $\beta$，在 $x\ge\operatorname{artanh}l$ 上有 $r_\beta\ge r_\beta(\operatorname{artanh}l)>0$，所以 $\partial_xy$ 及 $\partial_xv_\beta$ 有界。置 $A(v)=\sigma_v/(1-v)$，则 $A$ 及 $A'$ 在 $[c,d]$ 上有界，而且活动块的导数为
$$
 \frac{d}{du}[(1-u)A(v_\beta(u))]
 =-A(v_\beta(u))+
   \frac{A'(v_\beta(u))\,\partial_xv_\beta(u)}{1+u}.
$$
由于 $1+u\ge2a>0$，整条程序曲线的导数在开区间一致有界，其闭区间连续延拓因此为 Lipschitz 函数。本构造只实现（210.16）的具体无限集合，不声称实现任意预定无限集合。证毕。

点态 SLD 与秩变化处的连续信息量必须区分，相关一般公式见 Šafránek，*Discontinuities of the quantum Fisher information and the Bures metric*，Phys. Rev. A **95**, 052320（2017），定理1式（13）；有限维 SLD 的逆算子及伪逆表达见 Šafránek，*Simple expression for the quantum Fisher information matrix*，arXiv:1801.00945v2，式（4）—（5）、（12）—（13）。这里以（210.5）的残差等价式处理秩变化，并以处理器像的可微性、目标通道的仿射性和 $\mathcal T_{-1}$ 的非正性排除校准点聚集；有限性不以信息量自身连续或解析为前提。上述文献的 $C^2$ 秩变化修正公式不作为本节 $C^1$ 有限性结论的前提。

<a id="entry-770"></a>

## 追加锚（本行以下为增补区）

<a id="section-211"></a>

## 211. 精确校准附近的信息曲率及其维数无关最优值

**定义 211.1（点态校准的信息曲率）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$。考虑第187节的所有有限维固定 CPTP 程序：准备态 $\rho_u$ 在 $J_a$ 上为 $C^1$，同一个处理器对全部信号输入、全部 $u\in J_a$ 精确产生 $\mathcal T_u$，并满足 $I_Q(\rho_t)=I_r(t)$。仍取点态 SLD 信息量，令
$$
 \kappa(\rho,t)=\liminf_{\substack{u\to t\\u\ne t}}
       \frac{I_Q(\rho_u)-I_r(u)}{(u-t)^2},
 \qquad I_r(u)=\frac1{1-u^2}.
\tag{211.1}
$$
允许 $\kappa=+\infty$。记
$$
 h=\frac{1+t}{2},\quad \ell=1-h,\quad
 c_t=(1-t)(1+t)^2,\qquad
 V_*(a,t)=\frac14\left(
    \sqrt{1-\frac{a^2}{h}}+\sqrt{h-\frac{a^2}{h}}\right)^2.
\tag{211.2}
$$
由于 $a<h<1$，两个根号均严格为正，且 $0<V_*<1$。

**定理 211.2（任意有限维程序的统一校准曲率下界）。** 定义211.1中的每一个程序均满足
$$
 \kappa(\rho,t)\ge
 \kappa_*(a,t):=\frac{a^2}{c_t^2V_*(a,t)}.
\tag{211.3}
$$
该下界不要求实际准备态具有二阶导数，也不要求秩局部恒定。

证明。 先把第209节的受控等距归约推广到非仿射准备。令 $S$ 为全部实际程序态的支持所张成的子空间。由有限维性，可以选择有限多个实际程序态，其支持张成 $S$；这些态的严格正权平均在 $S$ 上满秩。对于任何信号基态 $|i\rangle$，各程序的输出均为 $|i\rangle\langle i|$，因而平均程序仍有同一纯输出。将平均态分解为正权本征投影，非负输出概率的和为零迫使原处理器的 Stinespring 等距在 $\mathbb C^3\otimes S$ 上具有受控形状。这里平均程序只用于证明原等距的结构，不要求平均态属于原参数曲线。

随后按第209.2节将处理器与交换信号标号 $0,2$ 后的处理器平均，再作其固定 Naimark 嵌入。其 Gram 正性、压缩分解和固定嵌入均不使用准备曲线的仿射性，所以得到固定算子与实际嵌入态
$$
 \sigma_u=J\rho_uJ^\dagger,\qquad
 P+Q=I,\quad PQ=0,\quad PT=T,\quad \|T\|_\infty\le1,
 \qquad
 \operatorname{Tr}(P\sigma_u)=\frac{1+u}{2},\quad
 \operatorname{Tr}(\sigma_uT)=a.
\tag{211.4}
$$
此处 $T$ 为第209.5式的 $\widetilde K$，固定等距嵌入保留 SLD 信息量。所有内点的双侧正性保证 $\sigma'_u$ 的核—核压缩为零，故存在有限点态 SLD $L_u$，包括秩变化点。置
$$
 H_u=\frac P{1+u}-\frac Q{1-u},\qquad
 \mathcal S_u(X)=\frac12(H_uX+XH_u),\qquad
 R_u=\sigma'_u-\mathcal S_u(\sigma_u),\qquad
 M=\frac{T+T^\dagger}{2}.
\tag{211.5}
$$
由第210.5式的平方残差恒等式，
$$
 g(u):=I_Q(\rho_u)-I_r(u)
      =\operatorname{Tr}[\sigma_u(L_u-H_u)^2],
 \qquad R_t=0.
\tag{211.6}
$$
读出概率导数给出 $\operatorname{Tr}R_u=0$。由于 $M$ 自伴，令 $D_u=L_u-H_u$，有
$\operatorname{Tr}(R_uM)=\operatorname{Re}\operatorname{Tr}[\sigma_uD_u(M-aI)]$。
对带权 Hilbert–Schmidt 内积使用 Cauchy–Schwarz，得到
$$
 |\operatorname{Tr}(R_uM)|^2
 \le g(u)\operatorname{Tr}[\sigma_u(M-aI)^2].
\tag{211.7}
$$
这一估计直接保留了 SLD 的平方范数，不对信息量取连续延拓。

下面计算左侧标量的一阶变化。按 $P\oplus Q$ 分块，记
$$
 x=\operatorname{Tr}(\sigma_{t,PP}T_{PP}),\qquad
 y=\operatorname{Tr}(\sigma_{t,QP}T_{PQ}).
$$
$PT=T$、常数期望及其导数给出
$$
 x+y=a,\qquad
 \frac{x}{1+t}-\frac{t\,y}{1-t^2}=0,
 \qquad x=at,\quad y=a(1-t).
\tag{211.8}
$$
第二个等式使用了 $\sigma'_t=\mathcal S_t(\sigma_t)$。它也说明 $x,y$ 均为实数，即使原算子不为实矩阵。

令 $K_u=\sqrt{(1+u)/2}\,P+\sqrt{(1-u)/2}\,Q$，并冻结辅助曲线
$\widehat\sigma_u=K_uK_t^{-1}\sigma_tK_t^{-1}K_u$。
这条辅助曲线光滑，满足 $\widehat\sigma'_u=\mathcal S_u(\widehat\sigma_u)$，并在 $t$ 与实际曲线具有相同的值和一阶导数。由（211.8），
$$
 \operatorname{Tr}(\widehat\sigma_uT)
 =\frac{1+u}{1+t}\,at
  +\frac{\sqrt{1-u^2}}{\sqrt{1-t^2}}\,a(1-t),
 \qquad
 \operatorname{Tr}(\widehat\sigma''_tT)=-\frac a{c_t}.
\tag{211.9}
$$
实际残差 $R$ 未必可微，但其标量像
$$
 e(u):=\operatorname{Tr}(R_uM)
      =-\operatorname{Tr}[\sigma_u\mathcal S_u(M)]
\tag{211.10}
$$
是 $C^1$：这里用到了 $\operatorname{Tr}(\sigma'_uM)=0$，而右侧只含 $C^1$ 实际态及光滑固定算子。对（211.10）求导，在 $t$ 使用 $\sigma'_t=\mathcal S_t(\sigma_t)$ 及 $\mathcal S_t$ 的迹配对自伴性，得到
$$
 e'(t)=-\operatorname{Tr}[
   (\mathcal S'_t(\sigma_t)+\mathcal S_t^2(\sigma_t))M]
 =-\operatorname{Tr}(\widehat\sigma''_tM)=\frac a{c_t}.
\tag{211.11}
$$
被求二阶导数的是辅助冻结曲线，未对实际曲线附加二阶光滑性。因此
$e(u)=(a/c_t)(u-t)+o(|u-t|)$。

还需证明名义态的统一方差界
$$
 \operatorname{Tr}[\sigma_t(M-aI)^2]\le V_*(a,t).
\tag{211.12}
$$
将 $\sigma_t$ 纯化为单位向量 $\psi$，并将 $P,Q,T$ 张量辅助恒等算子；全部算子关系及期望值保留。置 $p=P\psi$、$q=Q\psi$，则 $\|p\|^2=h$、$\|q\|^2=\ell$。第211.8式等价于
$\langle p,Tp\rangle=at$、$\langle p,Tq\rangle=2a\ell$。
对于 $k=T\psi$ 与 $r=T^\dagger p$，作相对于 $\operatorname{span}\{p,q\}$ 的正交分解，得到
$$
 k=\frac ahp+k_\perp,\qquad
 r=\frac{at}{h}p+2aq+r_\perp.
\tag{211.13}
$$
由于 $PT=T$，$k$ 没有 $q$ 分量；上述期望恒等式给出其余投影系数。压缩性给出
$$
 \|k_\perp\|^2\le1-\frac{a^2}{h},\qquad
 \|r_\perp\|^2
 \le h-\frac{a^2t^2}{h}-4a^2\ell
 =h-\frac{a^2}{h}.
\tag{211.14}
$$
又因 $T^\dagger\psi=T^\dagger p$ 及 $1+t=2h$，有
$(M-aI)\psi=(k_\perp+r_\perp)/2$。
三角不等式给出（211.12）。

最后，方差 $v(u)=\operatorname{Tr}[\sigma_u(M-aI)^2]$ 连续。对于任意 $\varepsilon>0$，充分接近 $t$ 时有 $v(u)\le V_*+\varepsilon$。将这一估计与（211.11）代入（211.7），再取下极限及 $\varepsilon\downarrow0$，得到（211.3）。此论证覆盖 $v(t)=0$、秩变化和信息量不连续的情形；其中没有使用 $R'_t$ 的存在。证毕。

**定理 211.3（实解析纯态程序的全局最优三维实现）。** 对每个定义211.1中的 $a,t$，存在一个固定三维 CPTP 处理器及一条在整个 $J_a$ 上实解析的纯态准备曲线，对所有参数和全部信号输入精确产生 $\mathcal T_u$，而且
$$
 \mathcal E(\rho)=\{t\},\qquad
 \lim_{\substack{u\to t\\u\ne t}}
 \frac{I_Q(\rho_u)-I_r(u)}{(u-t)^2}=\kappa_*(a,t).
\tag{211.15}
$$
因此，定义211.1中所有有限维 $C^1$ 程序的信息曲率下确界恰为 $\kappa_*$，并被三维实解析纯态程序达到；达到这个最优值并具有精确校准的最小联合支持维数恰为三。

证明。 首先在三维程序空间内构造达到最优值的局部纯态模型。所有以下算子一经 $a,t$ 选定便固定，不依赖待估参数 $u$。令
$$
 P_0=\operatorname{diag}(1,1,0),\qquad Z_0=2P_0-I,
 \qquad \psi_*=(\sqrt h,0,\sqrt\ell)^{\mathsf T},
 \qquad
 \gamma=\sqrt{1-\frac{a^2}{h^2}},\quad
 \alpha=\sqrt{1-\frac{a^2}{h}},
\tag{211.16}
$$
并置
$$
 r=\begin{pmatrix}at/h\\\gamma\\2a\sqrt{\ell/h}\end{pmatrix},
 \qquad s=\frac{\psi_*-(a/\sqrt h)r}{\alpha},
 \qquad
 T_0=\begin{pmatrix}r^{\mathsf T}\\s^{\mathsf T}\\0\quad0\quad0\end{pmatrix}.
\tag{211.17}
$$
由 $t^2+4h\ell=1$，有 $\|r\|=1$、$r^{\mathsf T}\psi_*=a/\sqrt h$；继而 $\|s\|=1$ 且 $r^{\mathsf T}s=0$。因此 $T_0T_0^\dagger=P_0$，$T_0$ 为压缩算子，且 $Z_0T_0=T_0$。定义固定等距映射
$$
 W_0=\binom{I_3}{0},\qquad
 W_2=\binom{Z_0}{0},\qquad
 W_1=\binom{T_0}{\sqrt{I_3-T_0^\dagger T_0}}.
\tag{211.18}
$$
受控等距 $\sum_{i=0}^2|i\rangle\langle i|\otimes W_i$ 后取环境偏迹，给出一个固定三维程序处理器。

令 $h(u)=(1+u)/2$、$\ell(u)=(1-u)/2$，考虑实单位向量及其通道系数
$$
 \psi(u,\theta)=\begin{pmatrix}
 \sqrt{h(u)}\cos\theta\\
 \sqrt{h(u)}\sin\theta\\
 \sqrt{\ell(u)}
 \end{pmatrix},\qquad
 f(u,\theta)=\psi(u,\theta)^{\mathsf T}T_0\psi(u,\theta).
\tag{211.19}
$$
此程序的 Schur 系数为 $C_{02}=u$、$C_{01}=C_{12}=f(u,\theta)$、$C_{ii}=1$。这是由（211.18）逐矩阵单位得到的恒等式；因为向量和算子均为实数，相关转置给出相同标量。因此 $f(u,\theta)=a$ 即保证对全部信号输入产生 $\mathcal T_u$。

置 $M_0=(T_0+T_0^\dagger)/2$。由（211.17）直接得到
$$
 T_0\psi_*=(a/\sqrt h,\alpha,0)^{\mathsf T},\qquad
 T_0^\dagger\psi_*=(at/\sqrt h,\sqrt h\,\gamma,2a\sqrt\ell)^{\mathsf T},
 \qquad (M_0-aI)\psi_*=\sqrt{V_*}\,(0,1,0)^{\mathsf T}.
\tag{211.20}
$$
这同时达到证明定理211.2时的方差界。取 $\theta=0$，曲线 $\psi(u,0)$ 正是 $\psi_*$ 的冻结等号曲线，所以（211.9）给出 $f(t,0)=a$、$f_u(t,0)=0$、$f_{uu}(t,0)=-a/c_t$。又由（211.20），
$$
 f_\theta(t,0)=2\sqrt h\sqrt{V_*}>0.
\tag{211.21}
$$
实解析隐函数定理因此给出 $t$ 的一个邻域上的实际函数 $\theta(u)$，满足 $f(u,\theta(u))=a$，且
$$
 \theta(t)=\theta'(t)=0,\qquad
 \theta''(t)=\frac{a}{2c_t\sqrt h\sqrt{V_*}}>0.
\tag{211.22}
$$
写 $\psi_u=\psi(u,\theta(u))$。实归一化向量满足 $\langle\psi_u,\psi'_u\rangle=0$，故普通纯态 SLD 信息量为 $4\|\psi'_u\|^2$。将（211.19）求导，得到精确恒等式
$$
 I_Q(|\psi_u\rangle\langle\psi_u|)-I_r(u)
       =4h(u)\theta'(u)^2.
\tag{211.23}
$$
结合（211.22），此局部模型的信息曲率恰为 $a^2/(c_t^2V_*)$。缩小邻域为 $I\Subset J_a$，可令 $\theta''>0$ 在 $I$ 上成立；于是 $\theta'$ 在 $I$ 内的唯一零点为 $t$。

下面证明这个局部纯态模型可以由同一个三维处理器解析延拓到整个 $J_a$。令 $Q_0=I-P_0$、$k=a/h$、$\beta=\sqrt h\,\gamma/\alpha$，则 $0<k,\beta<1$；后一个不等式来自 $\alpha^2-h\gamma^2=1-h>0$。在 $P_0\oplus Q_0$ 分块中写
$$
 T_0=\begin{pmatrix}\mathsf A&b\\0&0\end{pmatrix},\qquad
 \mathsf A=\begin{pmatrix}
 kt&\gamma\\
 \sqrt h(1-k^2t)/\alpha&-k\beta
 \end{pmatrix},\qquad
 b=\begin{pmatrix}2k\sqrt{h\ell}\\\sqrt\ell(1-2k^2h)/\alpha\end{pmatrix}.
\tag{211.24}
$$
由 $T_0T_0^{\mathsf T}=P_0$，有 $\mathsf A\mathsf A^{\mathsf T}+bb^{\mathsf T}=I_2$。计算得到 $\det\mathsf A=-\beta$，以及
$$
 \Delta:=\det(I_2-\mathsf A)
 =1-kt-(1-k)\beta
 =2(1-a)-(1-k)(1+\beta),\qquad
 0<k(1-t)<\Delta<2(1-a).
\tag{211.25}
$$
因此可以固定一个不依赖 $u$ 的方向
$$
 x=(I_2-\mathsf A)^{-1}b,\qquad N=\|x\|,\qquad
 e=\frac xN=(\cos\bar\theta,\sin\bar\theta)^{\mathsf T}.
\tag{211.26}
$$
直接求逆有
$x_1=\sqrt\ell(2k\sqrt h+\gamma/\alpha)/\Delta>0$，且
$\alpha x_2=\sqrt h(1-k)x_1+\sqrt\ell>0$，所以 $0<\bar\theta<\pi/2$。

这一固定方向满足四个恒等式：
$$
 N^2=\frac{2(1+\beta)}{\Delta},\qquad
 b^{\mathsf T}x=1+\beta,\qquad
 e^{\mathsf T}\mathsf Ae=1-\frac\Delta2,\qquad
 b^{\mathsf T}e=\frac{\Delta N}{2}>0.
\tag{211.27}
$$
为核对它们，先由 $bb^{\mathsf T}=I_2-\mathsf A\mathsf A^{\mathsf T}$ 得
$xx^{\mathsf T}=(I_2-\mathsf A)^{-1}+(I_2-\mathsf A^{\mathsf T})^{-1}-I_2$；取迹并使用二维逆矩阵公式，得到第一式。设 $s=\operatorname{Tr}\mathsf A$。从 $\det\mathsf A=-\beta$ 和上述正交关系得 $\|b\|^2=1-\beta^2$；Cayley–Hamilton 恒等式 $\mathsf A^2=s\mathsf A+\beta I_2$ 给出
$b^{\mathsf T}\mathsf Ab=-s\beta(1+\beta)$。因此
$b^{\mathsf T}x=[(1-s)(1-\beta^2)-s\beta(1+\beta)]/\Delta=1+\beta$。
其余两式由 $\mathsf Ax=x-b$ 得到。

将可变的 $P_0$ 概率记为 $p\in[a,1]$。取两个固定角度 $0$ 与 $\bar\theta$，相应实纯态的 $T_0$ 期望分别为
$$
 m_0(p)=kt\,p+2k\sqrt{h\ell}\sqrt{p(1-p)},
 \qquad m_0(h)=a,\quad m'_0(h)=0,
\tag{211.28}
$$
$$
 m_{\bar\theta}(p)
 =p\left(1-\frac\Delta2\right)
  +\frac{\Delta N}{2}\sqrt{p(1-p)}.
\tag{211.29}
$$
$m_0$ 严格凹，故 $m_0(p)\le a$，等号仅在 $p=h$。另一个期望在右端满足
$m_{\bar\theta}(1)-a=(1-k)(1+\beta)/2>0$；在左端满足
$m_{\bar\theta}(a)-a=(\Delta/2)[N\sqrt{a(1-a)}-a]>0$，因为
$N^2>(1+\beta)/(1-a)>a/(1-a)$。式（211.29）的凹性于是给出整个闭区间上的严格夹逼：
$$
 m_0(p)\le a<m_{\bar\theta}(p)
 \qquad(a\le p\le1).
\tag{211.30}
$$
两端和中间的所有期望都属于同一个 $T_0$，没有分别优化处理器。

还须排除所选根的折返。记 $A_0=\mathsf A_{11}$、$D_0=\mathsf A_{22}$、$C_0=\mathsf A_{12}+\mathsf A_{21}>0$、$E_0=b_1>0$、$F_0=b_2$，并令
$$
 \begin{aligned}
 \Phi(p,\theta)={}&p(A_0\cos^2\theta+D_0\sin^2\theta
                         +C_0\sin\theta\cos\theta)\\
 &+\sqrt{p(1-p)}(E_0\cos\theta+F_0\sin\theta).
 \end{aligned}
\tag{211.31}
$$
这就是向量 $(\sqrt p\cos\theta,\sqrt p\sin\theta,\sqrt{1-p})^{\mathsf T}$ 的 $T_0$ 期望。对每个 $p\in(a,1)$，方程 $\Phi(p,\theta)=a$ 在 $[0,\bar\theta)$ 内恰有一个根，且该根处 $\Phi_\theta>0$。证明分两种情形。

若 $F_0\ge0$，则在 $0<\theta<\pi/2$ 上
$$
 \frac{\Phi_\theta}{\sin\theta\cos\theta}
 =2p(D_0-A_0)+pC_0(\cot\theta-\tan\theta)
 +\sqrt{p(1-p)}\left(\frac{F_0}{\sin\theta}
                              -\frac{E_0}{\cos\theta}\right)
\tag{211.32}
$$
严格递减，且左右极限分别为正无穷和负无穷。所以 $\Phi$ 先严格增加后严格减少，仅有一个极大值。结合（211.30），在 $\bar\theta$ 之前恰有一次从下方穿过 $a$，根处导数严格为正；$p=h$ 时该根为零，直接求导同样严格为正。

若 $F_0<0$，则 $2k^2h>1$，因而 $h>1/2$ 及 $A_0>0>D_0$。置 $y=\sin\theta$、$q=\sqrt{p(1-p)}$ 及 $G(y)=\Phi(p,\arcsin y)$。直接求导得
$$
 G''(y)=2p(D_0-A_0)
       +\frac{pC_0y(2y^2-3)-qE_0}{(1-y^2)^{3/2}}<0.
\tag{211.33}
$$
因为 $G(0)\le a<G(\sin\bar\theta)$，严格凹性给出唯一根，且从该根到 $\sin\bar\theta$ 的割线斜率严格为正，故根处导数严格为正。这也覆盖 $p=h$、根为零的情形。

把唯一根记为 $\Theta(p)$。非零角导数给出每一点附近的解析隐函数，唯一性使这些局部函数在交叠处一致，因此得到整个 $(a,1)$ 上的实解析函数。此处已证明全域选根相容性，而非直接将局部隐函数定理当作全域延拓。置
$$
 \theta(u)=\Theta\!\left(\frac{1+u}{2}\right),\qquad
 \psi_u=\psi(u,\theta(u)),\qquad
 \rho_u=\psi_u\psi_u^{\mathsf T}.
\tag{211.34}
$$
这是同一个三维处理器的全区间、全输入精确纯态程序，在开区间实解析。它在 $t$ 附近与此前的局部隐函数重合，所以（211.22）—（211.23）给出所需最优曲率。

最后证明没有额外校准点。在整个 $0\le\theta\le\bar\theta$ 上，$E_0\cos\theta+F_0\sin\theta>0$：$F_0\ge0$ 时直接成立；$F_0<0$ 时除以 $\cos\theta$，所得函数随角度递减，但在 $\bar\theta$ 处仍由 $b^{\mathsf T}e>0$ 保持正性。因此对每个固定角度，$\Phi(p,\theta)$ 关于 $p$ 严格凹。由选根唯一性和（211.30），在 $0<\theta\le\bar\theta$ 上有 $\Phi(h,\theta)>a$。若 $p<h$，从根 $\Phi(p,\Theta(p))=a$ 到 $h$ 的割线斜率严格为正，凹性给出 $\Phi_p>0$；若 $p>h$，相同论证给出 $\Phi_p<0$。结合 $\Phi_\theta>0$，得到
$$
 \Theta'(p)<0\quad(p<h),\qquad
 \Theta'(p)>0\quad(p>h),\qquad
 \Theta'(h)=0.
\tag{211.35}
$$
于是（211.23）中的信息差值仅在 $u=t$ 为零，完整校准集合恰为 $\{t\}$。

定理211.2给出所有有限维 $C^1$ 程序的统一下界，而上述三维程序达到它。第190.2节对任意二维全区间精确程序给出
$I_Q(\rho_t)-I_r(t)\ge a^2/[(1+t)(1+t-2a^2)]>0$，一维也不能实现非恒定通道族。因此，达到最优曲率并具有精确校准的最小联合支持维数恰为三；限制为开区间实解析纯态程序仍是同一最小维数。证毕。

**定理 211.4（同一三维处理器中的光滑端点实现）。** 定理211.3的同一个三维处理器还具有一条全区间、全输入精确准备曲线，其矩阵元素在包含 $[2a-1,1]$ 的开邻域具有 $C^\infty$ 延拓，并在 $t$ 的一个邻域与定理211.3的纯态曲线完全相同。因此它也达到 $\kappa_*(a,t)$，其完整校准集合为包含 $t$ 的有限集合。此处不指定其他校准点。具有光滑端点的程序类也以三维达到同一最小曲率及最小联合支持维数。

证明。 先给出同一处理器的两个端点态。右端取
$$
 w=T_0\psi_*=(a/\sqrt h,\alpha,0)^{\mathsf T},\qquad
 \tau_1=ww^{\mathsf T}.
\tag{211.36}
$$
由（211.17），$\psi_*$ 属于 $T_0$ 的初始支持，所以 $\|w\|=1$、$T_0^{\mathsf T}w=\psi_*$。于是 $w^{\mathsf T}T_0w=\psi_*^{\mathsf T}w=a$，且 $\operatorname{Tr}(\tau_1P_0)=1$。

左端令
$v_-=(\sqrt a,0,\sqrt{1-a})^{\mathsf T}$、
$v_+=(\sqrt a\,e,\sqrt{1-a})^{\mathsf T}$，并记
$m_-=m_0(a)<a<m_+=m_{\bar\theta}(a)$。由（211.30），
$$
 \lambda=\frac{a-m_-}{m_+-m_-}\in(0,1),\qquad
 \tau_l=(1-\lambda)v_-v_-^{\mathsf T}+\lambda v_+v_+^{\mathsf T},
 \qquad l=2a-1.
\tag{211.37}
$$
这是密度矩阵，满足 $\operatorname{Tr}(\tau_lP_0)=a$、$\operatorname{Tr}(\tau_lT_0)=a$。因此仿射参考准备
$$
 B_u=\frac{1-u}{1-l}\tau_l+\frac{u-l}{1-l}\tau_1
\tag{211.38}
$$
在整个闭区间都满足 $\operatorname{Tr}(B_uT_0)=a$、$\operatorname{Tr}(B_uP_0)=(1+u)/2$，且为实对称密度矩阵。由固定处理器的逐矩阵单位恒等式，它对所有信号输入精确产生 $\mathcal T_u$。

取实光滑函数 $\eta:J_a\to[0,\pi/2]$，在 $t$ 的一个邻域恒等于零，在两个端点附近恒等于 $\pi/2$。用 $\rho_u^{\rm pure}$ 表示定理211.3的全区间纯态曲线，置
$$
 \rho_u^{\rm sm}
 =\cos^2\eta(u)\,\rho_u^{\rm pure}
  +\sin^2\eta(u)\,B_u.
\tag{211.39}
$$
这是同一个三维空间中的凸混合。两项均使用同一个固定处理器实现同一目标通道，所以处理器的线性性给出全域、全输入精确性。它在校准点附近与纯态模型相同，在端点附近等于仿射参考准备，因此具有所述矩阵延拓；不要求区间外延拓仍保持正性。

参数相关的混合不会消除准备成本。实际导数包含切换项：
$$
 (\rho_u^{\rm sm})'
 =\cos^2\eta\,(\rho_u^{\rm pure})'
  +\sin^2\eta\,B'_u
  +\sin(2\eta)\eta'(B_u-\rho_u^{\rm pure}).
\tag{211.40}
$$
在两个权重都非零处，为估计信息量可先保留一个正交准备标签，再将标签丢弃。丢弃标签是固定 CPTP 映射；其 SLD 信息单调性与保留标签时的直和公式给出
$$
 I_Q(\rho_u^{\rm sm})
 \le \cos^2\eta\,I_Q(\rho_u^{\rm pure})
    +\sin^2\eta\,I_Q(B_u)+4\eta'(u)^2.
\tag{211.41}
$$
这里是三维混合态的上界，不是同空间混合的直和等式；辅助标签仅用于证明估计，不加入实际程序寄存器。权重取零或一时 $\eta'=0$，相应的单项曲线直接给出点态信息量。对仿射参考准备再保留两个端点的准备标签，还得到
$$
 I_Q(B_u)\le\frac1{(u-l)(1-u)}\qquad(u\in J_a).
\tag{211.42}
$$
所以切换区域的信息成本有限，且已被（211.41）显式计入。在 $t$ 附近权重恒定为一，曲率完全保留为 $\kappa_*$。定理210.3给出完整校准集合的有限性；定理211.3的维数下界给出最小联合支持维数为三。

上述纯态曲线本身不能具有右端 $C^1$ 矩阵延拓。事实上，纯态的固定投影读出满足
$\|P_0\rho_u^{\rm pure}Q_0\|_2^2=p(u)(1-p(u))$，其中 $p(u)=(1+u)/2$。若在右端有 $C^1$ 延拓，由 $\operatorname{Tr}(Q_0\rho_1)=0$ 及正性得到端点交叉块为零，从而左侧为 $O((1-u)^2)$；右侧却渐近等于 $(1-u)/2$。矛盾。因此，开区间的全局纯态实现与具有光滑端点的实现是同一三维处理器上的两条不同准备曲线。证毕。

测量 Fisher 信息与 SLD 的一般关系见 Braunstein、Caves，*Statistical Distance and the Geometry of Quantum States*，Phys. Rev. Lett. **72**, 3439（1994），以及 Barndorff-Nielsen、Gill，*Fisher information in quantum statistics*，arXiv:quant-ph/9808009。秩变化处点态 SLD 与连续 Bures 信息的区别见 Šafránek，*Discontinuities of the quantum Fisher information and the Bures metric*，Phys. Rev. A **95**, 052320（2017），定理1式（13）。本节由全输入程序的固定压缩关系、校准点的两个期望约束及其方差上界，确定此通道族的最优局部曲率；实际三维实现的全域性由固定方向夹逼和唯一选根证明，不由逐点可行性替代。光滑端点构造使用同空间混合，信息估计中明确计入参数相关的切换项。

<a id="entry-772"></a>

## 追加锚（本行以下为增补区）

<a id="section-212"></a>

## 212. 复相位在纯三维程序中安排完整校准集合

**定义 212.1（固定三维相位处理器）。** 固定 $0<a<1$，记 $L=1-a$，选择
$$
 0<\delta<\min\left\{\frac L4,\frac{1-a^2}{16}\right\},\qquad
 \lambda=L-\delta,\quad B=2\sqrt{a\lambda},\quad
 p_\delta=\frac a{1-\delta},\quad u_\delta=2p_\delta-1.
\tag{212.1}
$$
因此 $a<p_\delta<1$、$2a-1<u_\delta<1$。在程序空间 $\mathbb C^3$ 上定义
$$
 P=\operatorname{diag}(1,1,0),\quad Q=I-P,\quad Z=2P-I,
 \qquad
 K=\begin{pmatrix}
 a-\lambda&\delta&B\\
 \delta&a&0\\
 0&0&0
 \end{pmatrix}.
\tag{212.2}
$$
参数域仍为 $J_a=(2a-1,1)$，目标通道仍为第187节的 $\mathcal T_u$，固定均衡读出的信息量为 $I_r(u)=1/(1-u^2)$。本节只要求纯态准备在开区间 $J_a$ 上光滑，不要求闭端点延拓。校准集合沿用定义210.1。

**定理 212.2（标量控制的解析纯三维程序）。** 定义212.1的 $K$ 为严格压缩算子。令
$$
 W_0=\binom{I_3}{0},\qquad W_2=\binom{Z}{0},\qquad
 W_1=\binom{K}{\sqrt{I_3-K^\dagger K}}.
\tag{212.3}
$$
这些固定等距映射定义受控 CPTP 处理器。记
$$
 p=\frac{1+u}{2},\quad q=1-p,\quad
 R(p)=\sqrt{\frac a\lambda}\sqrt{\frac qp},\quad
 \gamma=\frac\lambda{2\delta},\quad s_c=\frac\lambda L,
 \qquad
 G(s)=s^2+\gamma^2\left(s+s^{-1}-2\right)^2\quad(s>0).
\tag{212.4}
$$
若 $s:(a,1)\to(0,\infty)$ 为实解析函数，且
$$
 R(p)^2G(s(p))<1\qquad(a<p<1),
\tag{212.5}
$$
则下式定义同一个三维处理器的全区间、全输入精确纯态程序：
$$
 \begin{gathered}
 r=Rs,\qquad y=\gamma R\frac{(s-1)^2}{s},\qquad
 z=\sqrt{1-r^2-y^2},\qquad v=(r,y+iz)^{\mathsf T},\\
 \psi_u=(\sqrt p\,r,\sqrt p\,(y+iz),\sqrt q)^{\mathsf T},
 \qquad \rho_u=\psi_u\psi_u^\dagger.
 \end{gathered}
\tag{212.6}
$$
其校准条件恰为
$$
 I_Q(\rho_u)=I_r(u)
 \quad\Longleftrightarrow\quad
 s(p)=1,\qquad \frac{ds}{dp}(p)=\frac1{2p(1-p)}.
\tag{212.7}
$$
常数选择 $s=s_c$ 在全区间严格可行，且没有校准点。

证明。 $KK^\dagger$ 的 $P$ 块为
$$
 \begin{pmatrix}
 (a+\lambda)^2+\delta^2&\delta(2a-\lambda)\\
 \delta(2a-\lambda)&a^2+\delta^2
 \end{pmatrix}.
\tag{212.8}
$$
$I_2-(KK^\dagger)_{PP}$ 的两个对角元分别至少为 $\delta$ 与 $(1-a^2)/2$：前者等于 $2\delta(1-\delta)$，后者等于 $1-a^2-\delta^2$。又有 $|2a-\lambda|<2$，所以
$$
 \det\bigl[I_2-(KK^\dagger)_{PP}\bigr]
 \ge\frac{\delta(1-a^2)}2-4\delta^2
 >\frac{\delta(1-a^2)}4>0.
\tag{212.9}
$$
因此 $KK^\dagger<I_3$，所有（212.3）均为等距映射；程序空间维数为三，等距映射的六维值域是随后被取偏迹的环境。

由（212.5）有 $z>0$，第212.6式为归一化实解析向量。$K_{PP}$ 为实对称矩阵，其第三列只与实坐标 $r$ 耦合，所以期望 $f=\psi_u^\dagger K\psi_u$ 为实数。直接配方得到
$$
 f-a=p\bigl[2\delta r y-\lambda(r-R)^2\bigr]=0.
\tag{212.10}
$$
这里使用 $y=\gamma(r-R)^2/r$。又有 $\psi_u^\dagger Z\psi_u=u$、$ZK=K$。因此受控等距映射后取环境偏迹的三个非对角 Schur 系数为 $u,a,a$，对角系数为一；这逐个核对全部信号矩阵单位，故在全部输入上精确产生 $\mathcal T_u$。

以下点表示 $u$ 导数。由纯态信息公式 $I_Q=4(\|\dot\psi\|^2-|\psi^\dagger\dot\psi|^2)$，得到
$$
 I_Q(\rho_u)-I_r(u)
 =4p\left(\|\dot v\|^2-p|v^\dagger\dot v|^2\right)
 \ge4p(1-p)\|\dot v\|^2.
\tag{212.11}
$$
最后一步使用 $\|v\|=1$。这保留了复相位导数的成本，且校准当且仅当 $\dot v=0$。

用 $p$ 作自变量时，$v'=0$ 蕴含 $r'=y'=0$。在 $r'=0$ 处微分 $y=\gamma(r-R)^2/r$，得到
$y'=-2\gamma(r-R)R'/r$。因为 $R'\ne0$，必须 $r=R$。反过来，$r=R$、$r'=0$ 给出 $y'=0$，再由 $z>0$ 得 $z'=0$。因此校准等价于 $s=1$、$R'+Rs'=0$，而 $-R'/R=1/(2p(1-p))$，证明（212.7）。

函数 $s+s^{-1}-2$ 在正半轴非负且凸，故它的平方也凸；所以 $G$ 为凸函数，严格次水平集在正半轴为区间。常数 $s_c$ 满足
$$
 R(p)^2\le\frac1{s_c},\qquad
 G(s_c)=s_c^2+\frac{(1-s_c)^2}{4},\qquad
 R(p)^2G(s_c)\le s_c+\frac{(1-s_c)^2}{4s_c}<1,
\tag{212.12}
$$
因为 $3/4<s_c<1$。这个严格余量对 $p\in[a,1]$ 一致成立，其中仅在本式将 $R(1)$ 连续定义为零。常数 $s_c\ne1$，由（212.7）没有校准点。证毕。

**定理 212.3（任意有限完整校准集合的解析纯三维实现）。** 对定义212.1的固定处理器，任意有限集合 $S\subset(u_\delta,1)$ 都可成为某条全区间实解析纯态程序的完整校准集合。对非空集合 $S=\{t_1<\cdots<t_m\}$，标量控制 $s$ 可以是次数至多 $2m$ 的有理函数。

因此，$J_a$ 的任意有限集合均可由某个实解析纯三维程序精确实现；非空集合的最小联合程序支持维数恰为三。即使处理器固定、程序始终为纯态且在开区间解析，校准点数也没有统一有限上界。

证明。 空集由常数 $s_c$ 实现。其余情形令 $p_i=(1+t_i)/2>p_\delta$，于是 $R(p_i)^2<1$。定义
$$
 \begin{gathered}
 P_m(p)=\prod_{i=1}^m(p-p_i),\qquad
 L_i(p)=\frac{P_m(p)}{(p-p_i)P_m'(p_i)},\qquad
 \beta_i=\frac1{2p_i(1-p_i)},\\
 H(p)=1+\sum_{i=1}^m\beta_i(p-p_i)L_i(p)^2,\qquad
 s_k(p)=\frac{H(p)+k s_cP_m(p)^2}{1+kP_m(p)^2}\quad(k>0).
 \end{gathered}
\tag{212.13}
$$
第208节的 Hermite 插值结构在这里用于相位补偿坐标 $s$，不是该节的混合态准备坐标。直接代入给出
$$
 s_k(p_i)=1,\qquad s_k'(p_i)=\beta_i.
\tag{212.14}
$$

先核对整个参数区间的物理性。在每个 $p_i$ 的小邻域内，$H>0$ 且 $R^2G(H)<1$，因为在节点 $H=1$、$R^2<1$。$G$ 的凸性保证同一个 $p$ 处两个可行标量的凸组合仍可行，故（212.13）在这些邻域中满足（212.5）。在它们的补集 $[a,1]\setminus\bigcup_i U_i$ 上，$P_m^2$ 有正下界，而且
$$
 s_k(p)-s_c=\frac{H(p)-s_c}{1+kP_m(p)^2}\longrightarrow0
\tag{212.15}
$$
一致成立。由（212.12）的统一严格余量，充分大的 $k$ 保证整个 $[a,1]$ 上 $s_k>0$ 和 $R^2G(s_k)<1$。分母在实轴恒正，开区间内其余根号也严格为正，故定理212.2给出实际实解析纯态程序。

还须排除额外校准点。对 $p\notin\{p_i\}$，写
$$
 H(p)-1=P_m(p)^2\mathcal R(p),\qquad
 \mathcal R(p)=\sum_i\frac{\beta_i}{P_m'(p_i)^2(p-p_i)},
 \qquad \mathcal R'(p)<0.
\tag{212.16}
$$
因此 $s_k=1$ 的额外根满足 $\mathcal R=k(1-s_c)$，且在这些根处
$$
 s_k'=
 \frac{P_m^2\mathcal R'}{1+kP_m^2}<0.
\tag{212.17}
$$
它们不满足（212.7）所需的正导数。与（212.14）合并，完整校准集合恰为 $S$。分子、分母次数不超过 $2m$；此处只给有理控制次数上界，不声称最小次数或系数大小的统一界。

对任意有限非空 $S\subset J_a$，令 $p_{\min}=\min_{t\in S}(1+t)/2>a$，在（212.1）之外再取
$$
 \delta<1-\frac a{p_{\min}}.
\tag{212.18}
$$
这使全部节点满足 $p_i>p_\delta$。定理190.2排除任何联合支持维数至多二的全区间精确程序在内点达到 $I_r$，因此非空集合的最小联合支持维数恰为三。固定 $a,\delta$ 后，处理器不随节点个数或节点配置改变，只有 $s_k$ 改变。证毕。

**定理 212.4（固定纯三维中的无穷解析校准）。** 固定定义212.1的处理器，任选 $0<b<1-p_\delta$。存在全区间实解析纯态程序，精确生成全部 $\mathcal T_u$，其完整校准集合恰为
$$
 \mathcal E(\rho)=\left\{1-\frac{2b}{n}:n=1,2,\ldots\right\}.
\tag{212.19}
$$
这个集合只在参数域外的右端一聚集；最小联合程序支持维数仍为三。

证明。 对 $a<p<1$ 置
$$
 \omega(p)=\frac{2\pi b}{1-p},\qquad
 A(p)=\frac{1-p}{4\pi bp},\qquad
 H(p)=1+A(p)\sin\omega(p),\qquad
 D(p)=\sin^2\frac{\omega(p)}2,
\tag{212.20}
$$
并定义
$$
 s_k(p)=\frac{H(p)+k s_cD(p)}{1+kD(p)}.
\tag{212.21}
$$
由于 $b<1-p_\delta<1-a$，$D$ 在 $(a,1)$ 内的零点恰为
$p_n=1-b/n$，全部严格大于 $p_\delta$。在这些点 $D'=0$，而
$$
 A\omega'=\frac1{2p(1-p)},\qquad
 s_k(p_n)=1,\qquad s_k'(p_n)=\frac1{2p_n(1-p_n)}.
\tag{212.22}
$$

下面证明同一个有限 $k$ 可以保证全域物理性。$p\uparrow1$ 时 $H(p)\to1$、$R(p)^2\to0$，因此存在一个完整尾区间 $(p_*,1)$，其中 $H>0$ 且 $R^2G(H)<1$。结合（212.12）和 $G$ 的凸性，（212.21）在这个尾区间对全部 $k>0$ 都可行。在紧区间 $[a,p_*]$ 上，$D$ 只有有限个零点，每一个都满足 $H=1$、$R^2<1$，所以各有 $H$ 可行的小邻域。其余紧集上 $D$ 有严格正下界，而 $s_k\to s_c$ 一致成立。充分大的同一个 $k$ 于是保证所有 $a<p<1$ 满足 $s_k>0$ 和（212.5）。定理212.2给出全区间实解析纯态程序。

在 $D\ne0$ 处，$s_k=1$ 等价于
$$
 \mathcal R(p):=2A(p)\cot\frac{\omega(p)}2=k(1-s_c)>0.
\tag{212.23}
$$
由于 $A'<0$、$\omega'>0$，在这些额外根处 $\cot(\omega/2)>0$，所以
$$
 \mathcal R'
 =2A'\cot\frac\omega2-A\omega'\csc^2\frac\omega2<0,
 \qquad s_k'=\frac{D\mathcal R'}{1+kD}<0.
\tag{212.24}
$$
故额外根都不能校准；（212.22）中的节点全部校准，集合恰为（212.19）。维数下界再次来自定理190.2。这里不声称任意离散集合均有解析实现，也不要求右端 $C^1$ 延拓。证毕。

**定理 212.5（同一处理器的实纯态校准限制）。** 对定义212.1的固定处理器，若全区间精确的 $C^1$ 纯态准备 $\rho_u$ 在（212.2）的基底中始终为实矩阵，则
$$
 \mathcal E(\rho)\subseteq\{u_\delta\}.
\tag{212.25}
$$
因此定理212.3和212.4中任何非空校准集合的实现均不能在此固定基底中始终取实纯态。本结论针对同一个固定处理器，不是任意实处理器的校准点数上界。

证明。 精确的 $02$ 系数给出 $\operatorname{Tr}(Q\rho_u)=q>0$。实纯态因而具有唯一的第三分量为正的实归一化表示
$$
 \psi_u=(\sqrt p\,x(u),\sqrt p\,y(u),\sqrt q)^{\mathsf T},
 \qquad x^2+y^2=1.
\tag{212.26}
$$
此表示为 $C^1$，例如前两个分量分别等于 $\rho_{13}/\sqrt q$ 与 $\rho_{23}/\sqrt q$。实纯态的信息差值为 $4p[(x')^2+(y')^2]$，其中导数取 $u$，故校准时 $x'=y'=0$。将实际期望 $f=pA(x,y)+Bx\sqrt{pq}=a$ 与其参数导数联立，校准时有 $f_p=0$，消去 $A$ 得 $Bx=2a\sqrt{q/p}$，即 $x=R>0$。另一方面，精确期望的配方为
$$
 0=f-a=p[-\lambda(x-R)^2+2\delta xy].
\tag{212.27}
$$
所以校准时 $y=0$，继而 $x=1$、$R=1$，即 $p=p_\delta$、$u=u_\delta$。证毕。

纯态统计距离与相对相位导数的 Fisher 贡献见 Braunstein、Caves，*Statistical Distance and the Geometry of Quantum States*，Phys. Rev. Lett. **72**, 3439（1994），式（4）及其统计距离推导。固定受控量子处理器的一般形式见 Hillery、Ziman、Bužek，*Implementation of quantum maps by programmable quantum processors*，Phys. Rev. A **66**, 042302（2002），式（3.4）—（3.6）。本节使用这些标准工具，把同一个三维处理器的全输入精确条件化为相位补偿的平方恒等式，再以标量控制的值和一阶导数确定完整校准集合。维数固定不意味着准备成本有统一上界；第212.11式计入全部相位运动，未声称这些多点程序同时达到第211节的最优局部曲率。所有解析性均指开区间，未声称右端 $C^1$ 延拓。

<a id="entry-774"></a>

## 追加锚（本行以下为增补区）

<a id="section-213"></a>

## 213. 尖锐校准的谱容量与同一准备曲线的多点实现

**定义 213.1（同时尖锐校准及其维数）。** 固定 $`0<a<1`$，考虑第187节在 $`J_a=(2a-1,1)`$ 上全输入精确的固定 CPTP 程序，要求实际准备 $`\rho_u`$ 为 $`C^1`$ 纯态曲线。沿用定义211.1的双侧下极限曲率及定理211.2的最优值，置

```math
\mathcal E_*(\rho)=\{t\in J_a:I_Q(\rho_t)=I_r(t),\quad
                         \kappa(\rho,t)=\kappa_*(a,t)\}.
\tag{213.1}
```

称其中的点为尖锐校准点。对非空有限集合 $`S=\{t_1,\ldots,t_m\}\subset J_a`$，令 $`d_r(a,S)`$ 为满足 $`S\subseteq\mathcal E_*(\rho)`$ 的此类程序的最小联合支持维数，其中 $`r=1,\infty,\omega`$ 分别要求准备曲线为 $`C^1`$、$`C^\infty`$、实解析；实解析允许矩阵元素为复数。以下实向量构造是该类中的特例。对 $`h\in(a,1)`$ 定义

```math
\begin{gathered}
 b(h)=\sqrt{\frac{h^2-a^2}{h-a^2}},\qquad
 s(h)=\frac ah\bigl(2h-1-b(h)\bigr),\\[0pt]
 \lambda_\pm(h)=\frac{s(h)\pm\sqrt{s(h)^2+4b(h)}}2,\qquad
 N(a,S)=1+m+\#\{\lambda_-((1+t_i)/2):1\le i\le m\}.
 \end{gathered}
\tag{213.2}
```

负特征值按不同取值计数，不预设它随 $`h`$ 单调或逐点不同。

**定理 213.2（每个尖锐点强制原程序空间中的三维不变块）。** 对任意定义213.1程序，在其原联合支持 $`\mathcal H`$ 上按第209.3式固定对称化处理器，取相应的 $`A,K`$ 及 $`E=(I+A)/2`$。对每个尖锐校准点 $`t`$，记

```math
h=\frac{1+t}{2},\quad \ell=1-h,\quad
 \alpha=\sqrt{1-a^2/h},\quad \gamma=\sqrt{1-a^2/h^2},\quad
 c_t=(1-t)(1+t)^2,\quad V_*=(\alpha+\sqrt h\,\gamma)^2/4.
\tag{213.3}
```

存在原空间中的正交单位向量 $`e,z,f`$，使 $`Ee=e`$、$`Ez=z`$、$`Ef=0`$，并可选择名义纯向量为 $`\psi_t=\sqrt h\,e+\sqrt\ell\,f`$。子空间 $`\mathcal S_t=\operatorname{span}\{e,z,f\}`$ 被同一个固定算子 $`K^\dagger`$ 保持，且

```math
\begin{aligned}
 K^\dagger e&=\frac{at}{h}e+\gamma z+2a\sqrt{\ell/h}\,f,\\[0pt]
 K^\dagger z&=\frac{\psi_t-(a/\sqrt h)K^\dagger e}{\alpha},\qquad
 K^\dagger f=0.
 \end{aligned}
\tag{213.4}
```

因此这一限制酉等价于第211.17式的 $`T_0(a,t)^\dagger`$，其特征多项式为

```math
\det\bigl(xI-K^\dagger|_{\mathcal S_t}\bigr)
   =x\bigl(x^2-s(h)x-b(h)\bigr).
\tag{213.5}
```

这里不要求原空间上的整个 $`E`$ 是投影，不以 Naimark 扩大空间的维数代替实际程序维数。

证明。 第211.2节的有限忠实平均论证适用于任意固定处理器：选择有限多个实际准备态，其支持张成 $`\mathcal H`$，它们的严格正权平均在 $`\mathcal H`$ 上忠实。每个信号基态的输出仍为同一个纯基态，非负输出概率的零和迫使原 Stinespring 等距在整个联合支持上具有受控形式。随后作固定信号交换对称化，得到

```math
0\le E\le I,\quad KK^\dagger\le E,\qquad
 \langle\psi_u,E\psi_u\rangle=\frac{1+u}{2},\quad
 \langle\psi_u,K\psi_u\rangle=a.
\tag{213.6}
```

此处 $`K`$ 及 $`E`$ 不随校准点改变。选定 $`C=E^{+1/2}K`$，其中 $`E^{+1/2}`$ 表示在正谱上取逆平方根、在核上取零，故 $`K=\sqrt E\,C`$、$`\|C\|\le1`$。采用固定等距与扩大算子

```math
Jx=\sqrt E\,x\oplus\sqrt{I-E}\,x,\qquad
 T=\iota_+CJ^\dagger,\qquad
 P+Q=I,
\tag{213.7}
```

其中 $`P,Q`$ 为两个分量的投影，$`\iota_+`$ 为第一分量的嵌入。于是

```math
PT=T,\quad \|T\|\le1,\quad J^\dagger TJ=K,\quad
 \operatorname{ran}T^\dagger\subseteq\operatorname{ran}J.
\tag{213.8}
```

在 $`t`$ 附近选择 $`C^1`$ 单位向量表示及水平相位，令 $`\phi_u=J\psi_u`$、$`\langle\phi_u,\phi'_u\rangle=0`$。局部表示可由 $`\rho_u w/\sqrt{w^\dagger\rho_u w}`$ 再乘积分相位取得。写

```math
H_u=\frac P{1+u}-\frac Q{1-u},\qquad
 d(u)=\phi'_u-\frac12H_u\phi_u,\qquad
 M=\frac{T+T^\dagger}{2},\qquad v(u)=(M-aI)\phi_u.
\tag{213.9}
```

纯态信息公式和固定投影概率导数给出

```math
g(u):=I_Q(\rho_u)-I_r(u)=4\|d(u)\|^2.
\tag{213.10}
```

校准时 $`d(t)=0`$，所以 $`H_t\phi_t=2\phi'_t\in\operatorname{ran}J`$。由于 $`H_t`$ 的两个分量系数不同，$`p=P\phi_t`$、$`q=Q\phi_t`$ 均属于 $`\operatorname{ran}J`$。置 $`Je=p/\sqrt h`$、$`Jf=q/\sqrt\ell`$；由 $`J`$ 的定义得 $`Ee=e`$、$`Ef=0`$。

第211.10—211.14式的标量残差与方差界在纯态上为

```math
\varepsilon(u)=2\operatorname{Re}\langle d(u),v(u)\rangle,
 \qquad \frac{\varepsilon(u)}{u-t}\longrightarrow\frac a{c_t},
 \qquad \|v(t)\|^2\le V_*.
\tag{213.11}
```

选取实现尖锐下极限的序列 $`u_n\to t`$。由 Cauchy–Schwarz、（213.10）及 $`\kappa_*=a^2/(c_t^2V_*)`$，有

```math
\frac{a^2}{c_t^2}
 \le \kappa_*\|v(t)\|^2\le\kappa_*V_*=
 \frac{a^2}{c_t^2}.
\tag{213.12}
```

故方差界必须取等。第211.13式的正交分解给出

```math
T\phi_t=\frac ahp+k_\perp,\qquad
 T^\dagger p=\frac{at}{h}p+2aq+r_\perp,
 \qquad v(t)=\frac{k_\perp+r_\perp}{2},
\tag{213.13}
```

其中两个余向量均正交于 $`p,q`$，且 $`k_\perp\in\operatorname{ran}P`$。它们的范数上界分别为 $`\alpha`$、$`\sqrt h\,\gamma`$，均严格为正。方差取等迫使两个范数取等并正向共线。因此存在单位向量 $`\widetilde z`$，使

```math
k_\perp=\alpha\widetilde z,\qquad
 r_\perp=\sqrt h\,\gamma\widetilde z,\qquad
 \widetilde z\in\operatorname{ran}P\cap\{p,q\}^\perp.
\tag{213.14}
```

复 Hilbert 空间的三角等号同样要求正实比例，故这里没有未受约束的相对相位。由（213.8）及 $`p,q\in\operatorname{ran}J`$，$`r_\perp`$ 属于 $`\operatorname{ran}J`$；于是 $`\widetilde z=Jz`$，且 $`Ez=z`$。这把第三个方向放回原程序空间。

式（213.13）现在成为 $`T J\psi_t=(a/\sqrt h)Je+\alpha Jz`$。范数取等还给出 $`\|TJ\psi_t\|=1`$，压缩性因而蕴含 $`T^\dagger TJ\psi_t=J\psi_t`$。对这两个等式及 $`T^\dagger p`$ 的分解施加 $`J^\dagger`$，便得到（213.4）的前两式。由 $`KK^\dagger\le E`$ 及 $`Ef=0`$ 得最后一式。它们直接证明 $`\mathcal S_t`$ 对 $`K^\dagger`$ 不变。在同一正交基 $`(e,z,f)`$ 中，三列恰为 $`T_0^\dagger`$，而不是独立的左右基底变换。第211.24式给出其非零二维块的迹 $`s(h)`$ 和行列式 $`-b(h)`$，故得（213.5）。整个证明仅使用实际曲线的一阶可微性；二阶信息由可微的标量残差取得。证毕。

**定理 213.3（尖锐点数的维数界及三维位置签名）。** 任意有限维的定义213.1程序满足

```math
\#\mathcal E_*(\rho)\le \dim\mathcal H-2
 \quad\text{只要 }\mathcal E_*(\rho)\ne\varnothing,
 \qquad d_1(a,S)\ge N(a,S).
\tag{213.15}
```

特别地，维数至多三时至多存在一个尖锐校准点。若维数恰为三且存在尖锐点，则 $`E`$ 是秩二投影，$`KK^\dagger=E`$；固定压缩的读数

```math
D=\left|\det\left(EKE\big|_{\operatorname{ran}E}\right)\right|^2
\tag{213.16}
```

满足 $`0<D<1`$，且该点唯一可能的位置为

```math
t_*=D+\sqrt{D^2+4a^2(1-D)}-1.
\tag{213.17}
```

这些条件是必要条件，不单凭 $`D`$ 声称原处理器存在达到尖锐性的准备。

证明。 对每个 $`h\in(a,1)`$，有 $`0<b(h)<1`$。定理213.2的三维限制是压缩算子，因此其两个非零实特征值满足 $`-1\le\lambda_-<0<\lambda_+\le1`$。此外

```math
1-s(h)-b(h)
 =(1-a/h)(1-b(h))+2a(1/h-1)>0,
\tag{213.18}
```

故 $`\lambda_+<1`$。对其特征方程求导，得到

```math
\begin{aligned}
 b'(h)&=\frac{h^2-2a^2h+a^2}{2b(h)(h-a^2)^2}>0,\\[0pt]
 \lambda_+'(h)&=
 \frac{a(1+b(h))\lambda_+(h)/h^2+
             b'(h)(1-a\lambda_+(h)/h)}
      {2\lambda_+(h)-s(h)}>0.
 \end{aligned}
\tag{213.19}
```

分子各项严格为正，分母为 $`\sqrt{s(h)^2+4b(h)}`$。因此不同尖锐点强制同一个原算子 $`K^\dagger`$ 具有不同正特征值；此外还必须有零特征值及（213.2）列出的全部不同负特征值。这给出 $`\dim\mathcal H\ge N(a,S)`$。从任意有限尖锐点集应用此计数，便知整个尖锐集合也有限，且至多含 $`\dim\mathcal H-2`$ 个点。

三维时，定理213.2的 $`e,z,f`$ 已张成整个原空间，故 $`E`$ 是秩二投影，$`K`$ 在该基底恰为 $`T_0`$；第211.17式的两个非零行正交归一，故 $`KK^\dagger=E`$。同一投影分解下的酉相似不改变压缩行列式，因而

```math
D=b(h)^2=\frac{h^2-a^2}{h-a^2},\qquad
 \frac{dD}{dh}=\frac{(h-a^2)^2+a^2(1-a^2)}{(h-a^2)^2}>0.
\tag{213.20}
```

解 $`h^2-Dh-a^2(1-D)=0`$ 的正根，再取 $`t=2h-1`$，即得（213.17）。证毕。

**定理 213.4（谱下界维数中的共同处理器与分别准备）。** 对定义213.1的有限集合 $`S`$，存在维数 $`N(a,S)`$ 的同一个固定 CPTP 处理器，以及 $`m`$ 条分别定义在整个 $`J_a`$ 上的实解析纯态准备曲线。第 $`i`$ 条对全部信号输入精确实现 $`\mathcal T_u`$，完整校准集合与尖锐集合均为 $`\{t_i\}`$。这里是同一处理器上的多条曲线，不是同时经过全部指定尖锐点的一条曲线。

证明。 令 $`\Lambda`$ 为（213.2）中全部不同的零、正、负特征值。规定有限谱的部分等距构造是经典工具，见 Garcia、Sherman，*Matrices Similar to Partial Isometries*，arXiv:1703.02960v2，引理2及定理1；下面同时固定本题所需的各个三维压缩。

先对 $`\Lambda_0=\Lambda\cap(-1,1)`$ 取实向量 $`x_\lambda`$，规定其 Gram 矩阵为

```math
\langle x_\lambda,x_\mu\rangle=\frac1{1-\lambda\mu}
       =\sum_{n=0}^\infty\lambda^n\mu^n.
\tag{213.21}
```

不同实节点的 Vandermonde 独立性保证该矩阵正定：任一零二次型迫使所有幂矩为零，前 $`|\Lambda_0|`$ 个已经迫使系数全零。在这些线性无关向量张成的空间定义 $`Vx_\lambda=\lambda x_\lambda`$，置 $`q=x_0`$。式（213.21）给出 $`\|q\|=1`$、$`\langle q,x_\lambda\rangle=1`$，以及

```math
V^\dagger V=I-|q\rangle\langle q|=:P,
 \qquad T=V^\dagger,\qquad TT^\dagger=P,\quad PT=T.
\tag{213.22}
```

若 $`-1\in\Lambda`$，追加一个与前述空间正交的单位向量 $`x_{-1}`$，令 $`Vx_{-1}=-x_{-1}`$；式（213.22）仍成立。其余单位圆特征值由（213.18）排除。因此总维数为 $`|\Lambda|=N(a,S)`$，并未把发散的 $`1/(1-(-1)^2)`$ 当作 Gram 元素。

对每个 $`i`$，子空间

```math
\mathcal H_i=\operatorname{span}
       \{x_0,x_{\lambda_+(h_i)},x_{\lambda_-(h_i)}\},
 \qquad h_i=(1+t_i)/2,
\tag{213.23}
```

被 $`V`$ 保持，并且 $`V|_{\mathcal H_i}`$ 酉等价于 $`T_0(a,t_i)^\dagger`$。为证明该酉等价，记后者为 $`V_i`$，其核由第211.16式的第三基向量 $`f_i`$ 张成，且 $`V_i^\dagger V_i=I-|f_i\rangle\langle f_i|`$。它的三个特征值两两不同。若 $`V_i y_\lambda=\lambda y_\lambda`$ 且 $`|\lambda|<1`$，则

```math
(1-\lambda^2)\|y_\lambda\|^2
       =|\langle f_i,y_\lambda\rangle|^2>0.
\tag{213.24}
```

因此可以实数缩放使 $`\langle f_i,y_\lambda\rangle=1`$。对两个如此归一化的特征向量应用部分等距恒等式，得到
$`(1-\lambda\mu)\langle y_\lambda,y_\mu\rangle=1`$，恰为（213.21）。若有特征值 $`-1`$，压缩算子的单位模特征向量属于正交的约化子空间：范数取等先给出 $`V_i^\dagger V_i y=y`$，再由 $`V_i y=-y`$ 得 $`V_i^\dagger y=-y`$。它与全部内部特征向量正交，归一化即可对应 $`x_{-1}`$。这证明存在实等距 $`U_i:\mathbb R^3\to\mathcal H_i`$，使

```math
U_i^\dagger P U_i=P_0,\qquad
 VU_i=U_iT_0(a,t_i)^\dagger,\qquad
 U_i^\dagger T U_i=T_0(a,t_i).
\tag{213.25}
```

最后一式是压缩恒等式，不要求 $`\mathcal H_i`$ 被 $`T`$ 保持。

采用第211.18式的固定受控处理器，将 $`I_3,T_0,Z_0`$ 分别替换为 $`I,T,Z=2P-I`$。每个 $`U_i\psi_i(u)`$ 都有 $`P`$ 期望 $`(1+u)/2`$ 和 $`T`$ 期望 $`a`$，故逐矩阵单位给出同一精确目标通道。固定等距保留纯态信息量，所以将定理211.3的全域曲线分别嵌入这些子空间，就保留各自唯一的校准点及尖锐曲率。这个构造证明各局部尖锐模型可以共处于一个低维处理器；尚未把这些分别准备连成同一条受约束曲线。证毕。

**定理 213.5（一条全局解析曲线的同时尖锐实现）。** 定义213.1中的维数满足

```math
N(a,S)\le d_1(a,S)\le d_\infty(a,S)
             \le d_\omega(a,S)\le3m.
\tag{213.26}
```

右端存在一个实际固定处理器与一条全区间实解析纯态曲线达到，并且其完整校准集合与尖锐集合都恰为 $`S`$。两个不同指定点的边界具体为

```math
\begin{cases}
 5\le d_1\le d_\omega\le6,
       &\lambda_-(h_1)\ne\lambda_-(h_2),\\[0pt]
 4\le d_1\le d_\omega\le6,
       &\lambda_-(h_1)=\lambda_-(h_2).
 \end{cases}
\tag{213.27}
```

这些不等式不判定两点情况下五维或四维是否足够。

证明。 对每个 $`t_i`$，取定理211.3的全域实解析归一化实向量 $`\psi_i(u)`$ 及其固定处理器。令

```math
L_i(u)=\prod_{j\ne i}\frac{u-t_j}{t_i-t_j},\qquad
 g_i(u)=\frac{L_i(u)^3}{\sqrt{\sum_jL_j(u)^6}},\qquad
 \Psi_u=\bigoplus_{i=1}^m g_i(u)\psi_i(u).
\tag{213.28}
```

$`\sum_iL_i=1`$ 保证分母在实轴处处严格为正，故 $`g_i`$ 和 $`\Psi`$ 均实解析，且 $`\sum_i g_i^2=1`$。处理器先去除程序块间相干，再在第 $`i`$ 块使用对应的固定处理器；每一块都对全部信号输入实现相同的 $`\mathcal T_u`$，因此其归一化加权和仍精确。

记 $`G_i(u)=I_Q(\psi_i\psi_i^\dagger)-I_r(u)`$。实向量的归一化保证 $`\langle\psi_i,\psi'_i\rangle=0`$，所以实际纯态准备的信息差值为

```math
I_Q(\Psi_u\Psi_u^\dagger)-I_r(u)
   =\sum_i g_i(u)^2G_i(u)+4\sum_i g_i'(u)^2.
\tag{213.29}
```

其中第二项保留了参数相关块权重的准备成本，未将去相干后混合态的信息当作实际纯态的信息。若 $`u\notin S`$，所有 $`G_i(u)>0`$，故总差值严格为正。在 $`u=t_i`$ 附近置 $`\delta=u-t_i`$，则

```math
\begin{gathered}
 g_j=O(\delta^3),\quad g_j'=O(\delta^2)\quad(j\ne i),\\[0pt]
 g_i=1+O(\delta^6),\quad g_i'=O(\delta^5).
 \end{gathered}
\tag{213.30}
```

非名义块的 $`G_j`$ 在此内点有界，因而总差值在 $`t_i`$ 为零，并满足

```math
I_Q(\Psi_u\Psi_u^\dagger)-I_r(u)=G_i(u)+O(\delta^4),\qquad
 \lim_{u\to t_i}\frac{I_Q(\Psi_u\Psi_u^\dagger)-I_r(u)}{(u-t_i)^2}
       =\kappa_*(a,t_i).
\tag{213.31}
```

故两种完整集合均恰为 $`S`$。实际程序空间为 $`3m`$ 维，联合支持维数至多 $`3m`$，不要求总等于 $`3m`$。其余维数不等式来自定理213.3与准备正则性类别的包含关系。证毕。

<a id="entry-776"></a>

## 追加锚（本行以下为增补区）

<a id="section-214"></a>

## 214. 负谱纤维分岔与分别准备的精确容量

**定义 214.1（一个处理器可分别尖锐校准的位置集合）。** 固定 $`0<a<1`$ 和程序空间维数预算 $`d\ge1`$。对一个固定 CPTP 处理器 $`\mathcal G`$，令 $`\mathfrak P_\nu(\mathcal G;a)`$ 为全部在整个 $`J_a`$ 上全输入精确的纯态准备曲线，其中 $`\nu=1`$ 要求 $`C^1`$，$`\nu=\omega`$ 要求实解析。精确性、点态 SLD 信息和尖锐下极限均沿用定义213.1。置

```math
\mathcal C_\nu(\mathcal G;a)
 =\{t\in J_a:\exists\rho\in\mathfrak P_\nu(\mathcal G;a),\quad
                           t\in\mathcal E_*(\rho)\},
 \qquad \nu\in\{1,\omega\}.
\tag{214.1}
```

不同位置允许选择不同的完整准备曲线，处理器始终相同。记

```math
C_\nu(d,a)=\sup_{\dim\mathcal H\le d,\,\mathcal G}
                         \#\mathcal C_\nu(\mathcal G;a).
\tag{214.2}
```

这一定义不同于同一条准备曲线的尖锐集合大小。预算允许未使用的程序方向，不把它们计作某条曲线的实际联合支持。

**定理 214.2（每个负谱纤维至多三点）。** 沿用第213.2式的 $`b(h),s(h),\lambda_\pm(h)`$。对每个 $`0<r\le1`$，集合

```math
H_{a,r}=\{h\in(a,1):\lambda_-(h)=-r\}
\tag{214.3}
```

至多有三个元素。当 $`a\ge1/2`$ 时，每个纤维至多有一个元素；当 $`0<a<1/2`$ 时，存在非空开区间 $`U_a\subset(0,1)`$，使每个 $`r\in U_a`$ 的纤维都恰含三个元素。单位圆情形更精确地满足

```math
H_{a,1}=\begin{cases}
 \{a+2a^2\},&0<a<1/2,\\[0pt]
 \varnothing,&1/2\le a<1.
 \end{cases}
\tag{214.4}
```

证明。 特征方程 $`r^2+s(h)r-b(h)=0`$ 等价于

```math
b(h)=\frac{r[h(r+2a)-a]}{h+ar}.
\tag{214.5}
```

分母严格为正；实际解的右侧也必须严格为正。两边平方、清除正分母并消去 $`h>0`$，得到首一三次多项式

```math
\begin{aligned}
 P_{a,r}(h)={}&h^3+(-4a^2r^2-4ar^3+2ar-r^4)h^2\\[0pt]
 &+(4a^4r^2+4a^3r^3+a^2r^4+5a^2r^2-a^2+2ar^3)h\\[0pt]
 &-4a^4r^2-2a^3r^3-2a^3r-a^2r^2.
 \end{aligned}
\tag{214.6}
```

直接展开的恒等式为

```math
(h^2-a^2)(h+ar)^2-(h-a^2)r^2[h(r+2a)-a]^2
          =hP_{a,r}(h).
\tag{214.7}
```

所以每个实际纤维点都是 $`P_{a,r}`$ 的根。首项系数恒为一，故不可能出现零多项式，实根至多三个。反过来，若 $`h\in(a,1)`$、$`P_{a,r}(h)=0`$ 且 $`h(r+2a)-a>0`$，则两边正根唯一，平方关系恢复为（214.5）；于是 $`-r`$ 是特征方程的负根，确实属于该纤维。这一正号条件不能在使用三次方程构造实际点时省略。

当 $`r=1`$，式（214.6）分解为

```math
P_{a,1}(h)=(h-1)(h-a-2a^2)^2.
\tag{214.8}
```

$`h=1`$ 不在开区间内，另一个候选点 $`h=a+2a^2`$ 属于 $`(a,1)`$ 当且仅当 $`a<1/2`$。此点满足 $`h(1+2a)-a=4a^2(1+a)>0`$，所以确为实际点；重根不计作两个位置。

下面证明两个参数区域的纤维重数。令 $`c=a+2a^2`$，把三次多项式对 $`h`$ 的导数写成关于 $`r`$ 的 Bernstein 形式：

```math
\partial_hP_{a,r}(h)
 =\sum_{k=0}^4\binom4k B_k\,r^k(1-r)^{4-k},
\tag{214.9}
```

其中

```math
\begin{aligned}
 B_0={}&3h^2-a^2,\\[0pt]
 B_1={}&3h^2-a^2+ah,\\[0pt]
 B_2={}&3h^2-\frac{a^2}{6}
          +2ah\left(1-\frac{2a}{3}\right)+\frac{2a^4}{3},\\[0pt]
 B_3={}&3h(h-a)+4a(1-a)h
          +2a^4+a^3+\frac32a^2+\frac a2,\\[0pt]
 B_4={}&(h-c)(3h-c-2).
 \end{aligned}
\tag{214.10}
```

式（214.9）由展开幂次逐项核对。由于 $`0<a<h<1`$，前四个系数严格为正。若 $`a\ge1/2`$，则 $`c\ge1`$，所以 $`h-c<0`$、$`3h-c-2<0`$，第五个系数也严格为正。Bernstein 权重非负且总和为一，故对所有 $`0\le r\le1`$，$`\partial_hP_{a,r}(h)>0`$。每个固定 $`r`$ 因而至多有一个三次方程根，更至多有一个物理原像。

反之，设 $`0<a<1/2`$，记 $`R(h)=-\lambda_-(h)`$，以及 $`h_c=a+2a^2\in(a,1)`$。连续性、第213节的压缩性和（214.4）给出

```math
0<R(h)\le1,\qquad
 \lim_{h\downarrow a}R(h)=1-2a,\qquad
 R(h_c)=1,\qquad
 \lim_{h\uparrow1}R(h)=1,
\tag{214.11}
```

而且 $`h_c`$ 是唯一取值为一的内点。两个端点极限也可直接由 $`b(h)`$ 与 $`s(h)`$ 的定义计算。任选 $`h_M\in(h_c,1)`$，则 $`R(h_M)<1`$，所以

```math
U_a=\bigl(\max\{1-2a,R(h_M)\},1\bigr)
\tag{214.12}
```

是 $`(0,1)`$ 中的非空开区间。对每个 $`r\in U_a`$，中间值定理在 $`(a,h_c)`$、$`(h_c,h_M)`$、$`(h_M,1)`$ 中分别给出一个实际等式 $`R(h)=r`$ 的解。三段互不相交，且总纤维数至多三个，故每段恰有一解，整个纤维恰有三个元素。这一存在论证直接使用未平方的实际特征值函数。证毕。

**定理 214.3（分别准备与单曲线共同遵守的容量上界）。** 对所有定义214.1处理器及所有 $`0<a<1`$，有

```math
\#\mathcal C_1(\mathcal G;a)
 \le\left\lfloor\frac{3(d-1)}4\right\rfloor,
 \qquad C_\omega(d,a)\le C_1(d,a)
 \le\left\lfloor\frac{3(d-1)}4\right\rfloor.
\tag{214.13}
```

当 $`1/2\le a<1`$ 时，上界进一步收紧为

```math
C_\omega(d,a)\le C_1(d,a)\le
                 \left\lfloor\frac{d-1}{2}\right\rfloor.
\tag{214.14}
```

因此任意一条实际纯态 $`C^1`$ 准备曲线的尖锐集合也满足同一个界。若 $`0<a<1/2`$ 且 $`t_0=2a+4a^2-1`$ 属于该处理器的可分别尖锐校准集合，则还有

```math
\#\mathcal C_1(\mathcal G;a)
       \le\left\lfloor\frac{3d-5}4\right\rfloor.
\tag{214.15}
```

证明。 从 $`\mathcal C_1`$ 任取 $`m`$ 个不同位置，并为每个位置选择一条见证曲线。把这些曲线所有实际准备态的支持合并张成 $`\mathcal H_0`$，其维数不超过 $`d`$。可以从这些实际态中选择有限个，其支持张成 $`\mathcal H_0`$；严格正权平均在这个共同空间上忠实，并对每个信号基态保留同一纯输出。故第213.2节的受控等距与固定对称化归约在整个共同空间上产生同一对 $`E,K`$。每条曲线都满足相同的固定期望约束，其各自尖锐点的等号证明仍在这个共同空间中成立。因此不能通过换准备曲线来换掉被计数的算子 $`K^\dagger`$。

第213.19式说明这 $`m`$ 个位置贡献 $`m`$ 个不同正特征值；还必须有零特征值。定理214.2说明同一个负特征值最多被三个不同位置共享，所以负谱至少含 $`\lceil m/3\rceil`$ 个不同值。于是

```math
d\ge1+m+\lceil m/3\rceil
       =1+\lceil4m/3\rceil,
 \qquad m\le\left\lfloor\frac{3(d-1)}4\right\rfloor.
\tag{214.16}
```

此界适用于任意有限子集，因而整个位置集合也有限并满足该界。实解析准备是 $`C^1`$ 准备的子类，故得（214.13）。若 $`a\ge1/2`$，每个负谱纤维至多一个位置，因而相同论证给出

```math
d\ge1+2m,\qquad m\le\left\lfloor\frac{d-1}{2}\right\rfloor,
\tag{214.17}
```

这证明（214.14）。任意一条曲线的尖锐点都是同一个处理器可分别达到的点，所以上界也约束单曲线。

若所选位置包括 $`t_0`$，对应负特征值为 $`-1`$，其纤维由（214.4）仅含一个点。其余每个不同负特征值最多容纳三个点。设负特征值共有 $`n`$ 个，则 $`m\le1+3(n-1)`$，所以

```math
d\ge1+m+\left\lceil\frac{m+2}3\right\rceil,
 \qquad m\le\left\lfloor\frac{3d-5}4\right\rfloor.
\tag{214.18}
```

对包含 $`t_0`$ 的任意有限子集应用它，即得（214.15）。这里要求 $`t_0`$ 实际可尖锐校准；未使用的单位圆谱本身不替代这个前提。证毕。

**定理 214.4（分别准备容量的完整参数分界）。** 对每个 $`0<a<1`$ 及每个整数 $`d\ge1`$，有

```math
C_\omega(d,a)=C_1(d,a)=
 \begin{cases}
 \left\lfloor3(d-1)/4\right\rfloor,&0<a<1/2,\\[0pt]
 \left\lfloor(d-1)/2\right\rfloor,&1/2\le a<1.
 \end{cases}
\tag{214.19}
```

更具体地，对每个 $`m\ge1`$，存在恰含 $`m`$ 个位置的集合 $`S`$ 及一个固定处理器，使

```math
\mathcal C_\omega(\mathcal G;a)=\mathcal C_1(\mathcal G;a)=S,
 \qquad
 \dim\mathcal H=
 \begin{cases}
 1+m+\lceil m/3\rceil,&0<a<1/2,\\[0pt]
 1+2m,&1/2\le a<1.
 \end{cases}
\tag{214.20}
```

这些维数达到分别准备 $`m`$ 个尖锐位置的最小预算。每个位置由一条全区间实解析纯态曲线分别达到，各条曲线自身的完整校准集合与尖锐集合均只有这个位置。本定理不将这些曲线合并为一条同时达到全部位置的曲线。

证明。 先设 $`0<a<1/2`$，采用定理214.2给出的非空开区间 $`U_a`$。将 $`m`$ 写成 $`m=3k+j`$，其中 $`j\in\{0,1,2\}`$。从 $`U_a`$ 中选取 $`k`$ 个不同的负谱参数；若 $`j>0`$，再选一个不同参数。前 $`k`$ 组各取三个实际原像，最后一组按需取一根或两根，并置对应位置 $`t=2h-1`$。同一组的三个根不同；不同组也不可能共用一个根，因为单值函数 $`\lambda_-(h)`$ 不会同时等于两个不同的 $`-r`$。因此得到恰含 $`m`$ 点的 $`S`$，具有恰好 $`\lceil m/3\rceil`$ 个不同负特征值。第213.19式保证所有正特征值也不同。

若 $`a\ge1/2`$，直接在 $`(a,1)`$ 中任取 $`m`$ 个不同的 $`h`$。定理214.2保证负特征值两两不同，第213.19式保证正特征值两两不同，所以这时恰有 $`m`$ 个不同负特征值。

分别对这两个集合应用定理213.4，共同处理器所需维数为

```math
N=1+m+\#\{\lambda_-(h):2h-1\in S\}.
\tag{214.21}
```

该定理同时给出 $`m`$ 条分别准备的全域解析尖锐曲线。还须排除该处理器的额外可尖锐校准位置。其构造的固定读出为 $`P`$，系数为 $`T`$，满足 $`PT=T`$；受控处理器的对称化系数仍恰为 $`E=P,K=T`$。$`T`$ 的正特征值集合恰为已选 $`m`$ 个 $`\lambda_+(h)`$。对任何其他见证曲线，定理213.2的等号证明可以直接使用这一固定 $`P,T`$，尖锐位置必须再贡献一个 $`\lambda_+(h)`$。由该函数的严格单调性，它只能是已选的同一个 $`h`$。因此没有额外位置，得到（214.20）。若需在更大的程序预算空间中实现，可对 $`P,T`$ 作零直和并沿用第211.18式的受控构造；增加的零特征值不会创造新的正谱位置。

对 $`d\ge3`$，在低参数区域取 $`m=\lfloor3(d-1)/4\rfloor`$，则整数关系（214.16）给出 $`1+m+\lceil m/3\rceil\le d`$；在高参数区域取 $`m=\lfloor(d-1)/2\rfloor`$，则 $`1+2m\le d`$。因此解析准备达到相应的 $`C^1`$ 上界，证明（214.19）。$`d=1,2`$ 时两式上界均为零；取一个不依赖程序而只输出固定信号态的处理器，其可尖锐校准集合为空，即达到零。最小维数来自定理214.3的谱计数下界与已经给出的实际处理器。

同一条曲线的尖锐集合仍受（214.13）、（214.14）约束，但上述达到性选择了不同的完整准备曲线。尤其对两个负谱签名不同的指定点，本定理仍未把第213.27式的五维下界提升为单曲线的实际达到值。证毕。

<a id="entry-778"></a>

## 追加锚（本行以下为增补区）

<a id="section-215"></a>

## 215. 混态单曲线的最小尖锐维数与精确容量

**定义 215.1（允许秩变化的同时尖锐准备）。** 固定 $`0<a<1`$，沿用第211节的全输入精确目标族、点态 SLD 信息量和双侧下极限曲率。现允许实际准备 $`\rho_u`$ 为任意密度矩阵，不要求纯态，也不要求其秩局部恒定。令

```math
\mathcal E_*(\rho)=\{t\in J_a:I_Q(\rho_t)=I_r(t),\quad
                              \kappa(\rho,t)=\kappa_*(a,t)\}.
\tag{215.1}
```

对非空有限集合 $`S=\{t_1,\ldots,t_m\}\subset J_a`$，记 $`d_r^{\rm mix}(a,S)`$ 为一个固定处理器和一条完整准备曲线满足 $`S\subseteq\mathcal E_*(\rho)`$ 所需的最小联合支持维数，其中 $`r=1,\infty,\omega`$ 分别要求矩阵元素为 $`C^1`$、$`C^\infty`$、实解析。联合支持仍指全部实际准备态的支持张成空间。沿用第213.2式的 $`b(h),s(h),\lambda_\pm(h)`$ 与

```math
N(a,S)=1+m+\#\{\lambda_-((1+t_i)/2):1\le i\le m\}.
\tag{215.2}
```

**定理 215.2（混态尖锐点强制原算子的谱签名）。** 对任意定义215.1的 $`C^1`$ 程序，在原联合支持空间 $`\mathcal H`$ 上固定第213.6式的 $`E,K`$。每个尖锐点 $`t`$ 都强制

```math
\{0,\lambda_+((1+t)/2),\lambda_-((1+t)/2)\}
                       \subseteq\operatorname{spec}(K^\dagger).
\tag{215.3}
```

因此任意非空有限尖锐点集 $`S`$ 满足

```math
\dim\mathcal H\ge N(a,S),\qquad
\#\mathcal E_*(\rho)\le\dim\mathcal H-2
       \quad\text{若 }\mathcal E_*(\rho)\ne\varnothing.
\tag{215.4}
```

这里的谱属于原程序算子；证明所用的纯化空间不计入程序维数。

证明。 第211.2节的有限忠实平均与固定对称化归约适用于混态曲线，得到同一对 $`E,K`$。取第213.7式的固定 Naimark 等距 $`J`$ 及 $`T`$，并记

```math
\sigma_u=J\rho_uJ^\dagger,\qquad
\mathcal R=\operatorname{ran}J,\qquad
\Pi=JJ^\dagger,\qquad M=(T+T^\dagger)/2.
\tag{215.5}
```

它们满足 $`PT=T`$、$`\|T\|\le1`$、$`J^\dagger TJ=K`$ 及 $`\operatorname{ran}T^\dagger\subseteq\mathcal R`$。固定等距保留点态 SLD 信息。置 $`g(u)=I_Q(\rho_u)-I_r(u)`$ 与
$`v(u)=\operatorname{Tr}[\sigma_u(M-aI)^2]`$。第211.7、211.11式给出

```math
e(u)^2\le g(u)v(u),\qquad
 \frac{e(u)}{u-t}\longrightarrow\frac a{c_t},\qquad
 v(t)\le V_*(a,t),\qquad c_t=(1-t)(1+t)^2.
\tag{215.6}
```

$`v`$ 连续。取实现尖锐下极限的序列 $`u_n\to t`$，便有

```math
\frac{a^2}{c_t^2}\le\kappa_*(a,t)v(t)
       \le\kappa_*(a,t)V_*(a,t)=\frac{a^2}{c_t^2}.
\tag{215.7}
```

因此名义方差必须取等：$`v(t)=V_*`$。

将固定扩大空间上的算子记为
$`H_t=P/(1+t)-Q/(1-t)`$。校准等号给出 $`\sigma'_t=(H_t\sigma_t+\sigma_tH_t)/2`$。由于 $`\sigma_t`$ 和 $`\sigma'_t`$ 均支持在固定空间 $`\mathcal R`$ 中，左乘 $`I-\Pi`$ 得

```math
(I-\Pi)H_t\sigma_t=0,\qquad
 H_t\operatorname{supp}\sigma_t\subseteq\mathcal R.
\tag{215.8}
```

第二式只用到 $`\sigma_t`$ 在其支持上可逆，不要求邻近参数处具有相同的秩。

现在只在 $`t`$ 这个单独位置选择静态纯化。若 $`\sigma_t=\sum_jp_j|x_j\rangle\langle x_j|`$，其中 $`p_j>0`$，取辅助正交基 $`\epsilon_j`$ 并置

```math
\varphi=\sum_j\sqrt{p_j}\,x_j\otimes\epsilon_j,
 \qquad \widetilde T=T\otimes I,\quad
 \widetilde P=P\otimes I,\quad\widetilde Q=Q\otimes I.
\tag{215.9}
```

由（215.8），$`\varphi`$ 与 $`(H_t\otimes I)\varphi`$ 均在 $`\mathcal R\otimes\mathcal F`$ 内。$`H_t`$ 在 $`P,Q`$ 两个分量上的系数不同，故

```math
p=\widetilde P\varphi\in\mathcal R\otimes\mathcal F,
 \qquad q=\widetilde Q\varphi\in\mathcal R\otimes\mathcal F,
 \qquad \|p\|^2=h,\quad\|q\|^2=\ell,
 \quad h=(1+t)/2,\quad\ell=1-h.
\tag{215.10}
```

对这份静态纯化应用第211.13—211.14式的正交分解。方差已经取等，三角不等式和两个范数界因而同时取等。令
$`\alpha=\sqrt{1-a^2/h}>0`$、$`\gamma=\sqrt{1-a^2/h^2}>0`$，便有一个单位向量 $`\widetilde z`$，正交于 $`p,q`$，使

```math
\widetilde T\varphi=\frac ahp+\alpha\widetilde z,
 \qquad
\widetilde T^\dagger p=\frac{at}{h}p+2aq+
                             \sqrt h\,\gamma\widetilde z,
 \qquad \widetilde P\widetilde z=\widetilde z.
\tag{215.11}
```

$`\operatorname{ran}\widetilde T^\dagger\subseteq\mathcal R\otimes\mathcal F`$，再结合（215.10）和第二式，得到 $`\widetilde z\in\mathcal R\otimes\mathcal F`$。所以三个正交方向都能通过 $`J^\dagger\otimes I`$ 回到 $`\mathcal H\otimes\mathcal F`$。记其归一化像为 $`e,z,f`$，并置 $`\psi=\sqrt h\,e+\sqrt\ell\,f`$、$`\widehat K=K^\dagger\otimes I`$。由 $`J`$ 的形式可得
$`(E\otimes I)e=e`$、$`(E\otimes I)z=z`$、$`(E\otimes I)f=0`$。

第一式的范数为一，压缩性给出 $`\widetilde T^\dagger\widetilde T\varphi=\varphi`$。将（215.11）及此等式施加 $`J^\dagger\otimes I`$，再用 $`KK^\dagger\le E`$，得到

```math
\begin{aligned}
 \widehat K e&=\frac{at}{h}e+\gamma z+2a\sqrt{\ell/h}\,f,\\[0pt]
 \widehat K z&=\frac{\psi-(a/\sqrt h)\widehat K e}{\alpha},
 \qquad \widehat K f=0.
\end{aligned}
\tag{215.12}
```

因而 $`\operatorname{span}\{e,z,f\}`$ 是 $`K^\dagger\otimes I`$ 的三维不变子空间，限制的矩阵正是第213.4式，特征多项式为
$`x(x^2-s(h)x-b(h))`$。有限维算子的不变子空间特征值属于整个算子的谱，而

```math
\operatorname{spec}(K^\dagger\otimes I_{\mathcal F})
                         =\operatorname{spec}(K^\dagger).
\tag{215.13}
```

所以得到原算子的（215.3）。辅助维数只增加特征值的重数，不增加不同特征值，也没有进入维数下界。这里没有选择可微纯化，更没有把秩变化的点态信息量替换为连续延拓。

最后，第213.19式保证 $`\lambda_+`$ 严格递增；不同尖锐点贡献不同的正特征值，还必须保留零及全部不同的负特征值。对任意有限子集计数即得（215.4），并排除无限尖锐集合。证毕。

**定理 215.3（一条解析混态曲线达到精确最小维数）。** 对每个定义215.1中的 $`a,S`$，有

```math
d_1^{\rm mix}(a,S)=d_\infty^{\rm mix}(a,S)
                  =d_\omega^{\rm mix}(a,S)=N(a,S).
\tag{215.14}
```

存在一个固定 $`N(a,S)`$ 维处理器和一条全区间实解析混态准备，其完整尖锐集合恰为 $`S`$。在每个 $`t_i`$，曲率的双侧普通极限存在且等于 $`\kappa_*(a,t_i)`$；不只具有相同下极限。还可要求准备态在 $`S`$ 上秩为一、在 $`J_a\setminus S`$ 上处处至少为二。

证明。 采用定理213.4在同一个 $`N=N(a,S)`$ 维空间上构造的固定 $`P,T`$、处理器及分别准备的实解析纯态曲线 $`\rho_i(u)`$。它们对所有参数、所有信号输入实现同一目标通道。令

```math
L_i(u)=\prod_{j\ne i}\frac{u-t_j}{t_i-t_j},\qquad
 g_i(u)=\frac{L_i(u)^3}{\sqrt{\sum_jL_j(u)^6}},\qquad
 \rho_u=\sum_i g_i(u)^2\rho_i(u).
\tag{215.15}
```

$`\sum_iL_i=1`$ 保证分母在实轴上严格为正，所以权重和密度矩阵均实解析。$`\sum_i g_i^2=1`$ 保证 $`\rho_u`$ 是同一空间上的密度矩阵。处理器固定且线性，各分量实现的通道相同，故这一实际混态曲线全域、全输入精确。实际程序空间仍是 $`N`$ 维。

必须计入依赖参数的混合权重所携带的信息。为估计而暂时保留正交标签，取

```math
\tau_u=\bigoplus_i g_i(u)^2\rho_i(u),\qquad
 G_i(u)=I_Q(\rho_i(u))-I_r(u).
\tag{215.16}
```

丢弃标签是固定 CPTP 映射。SLD 信息的单调性与正权直和公式给出

```math
0\le I_Q(\rho_u)-I_r(u)
 \le\sum_i g_i(u)^2G_i(u)+4\sum_i g_i'(u)^2.
\tag{215.17}
```

这是参数相关混合的经典扩展凸性上界，见 Alipour、Rezakhani，*Quantum Metrology: Extended Convexity of Quantum Fisher Information*，Phys. Rev. A **91**, 042104（2015），arXiv:1403.8033v2，式（4）。这里的标签仅用于上界，不属于实际程序寄存器。左侧非负来自精确程序的固定测量读出，不是混合凸性结论。

还须核对权重为零时的点态含义。在所有权重非零处，经典权重项为
$`\sum_i[(g_i^2)']^2/g_i^2=4\sum_i(g_i')^2`$。权重取零只可能在 $`S`$；三次零点保证此处对应的 $`g_i'=0`$，零块和零块导数都为零，对点态 SLD 不作贡献。保留的唯一权重为一且其导数也为零。因此（215.17）在这些点同样成立，没有通过取极限向点态 SLD 添加权重出生项。单点集合的权重恒为一，也满足该论证。

在 $`t_i`$ 附近令 $`\delta=u-t_i`$，则

```math
\begin{gathered}
 g_j=O(\delta^3),\quad g_j'=O(\delta^2)\quad(j\ne i),\\[0pt]
 g_i=1+O(\delta^6),\quad g_i'=O(\delta^5),\\[0pt]
 \rho_{t_i}=\rho_i(t_i),\qquad \rho'_{t_i}=\rho_i'(t_i).
\end{gathered}
\tag{215.18}
```

点态 SLD 信息只取决于态及其一阶导数，故 $`I_Q(\rho_{t_i})=I_r(t_i)`$。各 $`G_j`$ 在该内点邻域有界，定理211.3及固定等距保留给出

```math
\begin{aligned}
 I_Q(\rho_u)-I_r(u)&\le G_i(u)+O(\delta^4),\\[0pt]
 \limsup_{u\to t_i,\,u\ne t_i}
 \frac{I_Q(\rho_u)-I_r(u)}{(u-t_i)^2}
 &\le\kappa_*(a,t_i).
\end{aligned}
\tag{215.19}
```

实际混态曲线已具有校准，所以定理211.2提供反向下极限界。两者夹逼，得到普通双侧极限等于 $`\kappa_*`$。这覆盖名义点与邻近点的秩不同的情形，不使用混态信息关于参数的连续性。

为了排除额外尖锐位置，使用共同处理器在完整 $`N`$ 维空间上的固定系数 $`E=P,K=T`$。定理215.2的证明只需这些固定算子关系与期望约束，所以也可直接在此空间应用；其正谱恰为已选的 $`m`$ 个 $`\lambda_+((1+t_i)/2)`$。任何额外尖锐位置都会强制一个新的正特征值，与严格单调性矛盾。因此

```math
\mathcal E_*(\rho)=S.
\tag{215.20}
```

实际联合支持维数至多为 $`N`$，而定理215.2对这条实际曲线的联合支持又给出至少 $`N`$，所以它恰为 $`N`$。最后，解析曲线属于光滑和 $`C^1`$ 类，与统一下界一起给出（215.14）。

最后加强实际混态的秩条件。在同一处理器的一块三维嵌入中，取定理211.4的仿射精确准备 $`B_u`$。其左端态是两个不同纯态的严格凸组合，故秩至少为二；在每个 $`u\in J_a`$，仿射组合中的左端权重严格为正，所以 $`\operatorname{rank}B_u\ge2`$，而（211.42）给出局部有界的 SLD 信息。令

```math
F(u)=\prod_i(u-t_i),\qquad
 \eta(u)=\frac{F(u)^6}{1+F(u)^6},\qquad
 \widetilde\rho_u=(1-\eta(u))\rho_u+\eta(u)B_u.
\tag{215.21}
```

这仍是同一空间、同一处理器的解析精确准备。在 $`S`$ 上其态及一阶导数保持不变；在 $`S`$ 外，$`\eta>0`$ 与正性给出秩至少为二。对这个二项混合再次使用扩展凸性，额外权重成本在 $`u\notin S`$ 为

```math
\frac{\eta'(u)^2}{\eta(u)(1-\eta(u))}
 =\frac{36F(u)^4F'(u)^2}{(1+F(u)^6)^2}
 =O((u-t_i)^4)\qquad(u\to t_i).
\tag{215.22}
```

又因 $`\eta=O((u-t_i)^6)`$，加入 $`B_u`$ 不改变最优二阶曲率；在零权重处其导数为零，仍按点态 SLD 计算。相同正谱排除论证给出 $`\mathcal E_*(\widetilde\rho)=S`$，同一个维数下界保证其实际联合支持也恰为 $`N`$。因此得到所要求的秩变化实现。

特别地，两个不同指定点的最小混态维数在负谱签名不同的情形恰为五，在负谱签名相同的情形恰为四。这不判定纯态单曲线是否能达到同一维数。式（215.20）只指定完整尖锐集合；其余非尖锐的普通校准点没有在本证明中被排除。证毕。

**定理 215.4（同一混态曲线的精确尖锐容量）。** 对整数 $`d\ge3`$，在程序预算维数不超过 $`d`$ 的全部定义215.1程序中，实解析曲线和 $`C^1`$ 曲线的最大尖锐点数相同，且为

```math
\max_{\dim\mathcal H\le d,\ \rho\ \mathrm{analytic}}
             \#\mathcal E_*(\rho)
 =\max_{\dim\mathcal H\le d,\ \rho\in C^1}
             \#\mathcal E_*(\rho)
 =\begin{cases}
 \left\lfloor3(d-1)/4\right\rfloor,&0<a<1/2,\\[0pt]
 \left\lfloor(d-1)/2\right\rfloor,&1/2\le a<1.
 \end{cases}
\tag{215.23}
```

这些最大值由一个固定处理器和一条实际准备曲线达到。程序预算至多二时，任何存在的精确准备曲线都没有尖锐点；本句不声称一维中存在全区间精确准备。

证明。 定理215.2将混态尖锐集合的计数归约为同一个原算子的不同特征值。定理214.2说明，低参数区域每个负谱纤维至多含三个点，高参数区域至多含一个点。因此 $`m`$ 个尖锐点分别要求
$`d\ge1+m+\lceil m/3\rceil`$ 或 $`d\ge1+2m`$，得到（215.23）的上界。至多二维的结论直接来自每个尖锐点强制三个不同特征值。

达到性沿用定理214.4选择的实际位置集合：低参数区域取互不相同的负谱纤维及其三重原像，最后一组按所需点数截取；高参数区域取任意不同位置。这分别给出 $`N=1+m+\lceil m/3\rceil`$ 和 $`N=1+2m`$。取（215.23）对应的最大整数 $`m\ge1`$，则 $`N\le d`$。定理215.3在这一维数中给出一条实际解析混态曲线，其完整尖锐集合恰是所选集合，故两个上界均达到。证毕。

<a id="entry-780"></a>

## 追加锚（本行以下为增补区）


<a id="section-216"></a>

## 216. 尖锐校准的秩成本与单位圆例外

**定义 216.1（指定名义秩的尖锐维数）。** 固定 $`0<a<1`$、$`t\in J_a`$ 及整数 $`r\ge1`$，令 $`D_\nu(a,t;r)`$ 为第215节混态程序满足 $`t\in\mathcal E_*(\rho)`$ 和 $`\operatorname{rank}\rho_t=r`$ 所需的最小实际联合支持维数，其中 $`\nu=1,\infty,\omega`$ 分别要求完整准备曲线为 $`C^1`$、光滑、实解析。仍使用点态 SLD 信息，允许曲线在别处改变秩。记

```math
h=(1+t)/2,\qquad h_c=a+2a^2,\qquad
 V=T_0(a,t)^\dagger,\quad
 \psi_0=(\sqrt h,0,\sqrt{1-h})^{\mathsf T},\quad
 f=(0,0,1)^{\mathsf T}.
\tag{216.1}
```

$`T_0`$ 为第211.17式的固定三维尖锐模型，满足 $`V^\dagger V=I-|f\rangle\langle f|`$。临界位置 $`h=h_c`$ 属于 $`(a,1)`$ 当且仅当 $`a<1/2`$。

**定理 216.2（名义秩的原空间维数下界）。** 每个定义216.1的 $`C^1`$ 程序都满足

```math
\dim\mathcal H\ge
 \begin{cases}
 3r,&h\ne h_c,\\[0pt]
 \max\{3,r+1\},&h=h_c.
 \end{cases}
\tag{216.2}
```

在非临界情形，原空间包含 $`r`$ 个两两正交的三维 $`K^\dagger`$ 不变子空间，每个限制都酉等价于 $`V`$。

证明。 在第215.2节中选择 $`\rho_t=\sum_{j=1}^r p_j|x_j\rangle\langle x_j|`$ 的谱纯化，$`p_j>0`$ 且 $`x_j`$ 正交归一。把回到 $`\mathcal H\otimes\mathbb C^r`$ 的三个正交向量按辅助基逐分量展开，得到线性映射 $`A_j:\mathbb C^3\to\mathcal H`$，满足

```math
K^\dagger A_j=A_jV,\qquad
 \sum_jA_j^\dagger A_j=I_3,\qquad
 A_j\psi_0=\sqrt{p_j}\,x_j.
\tag{216.3}
```

此处每个 $`A_j`$ 单独不预设为等距。令

```math
Q_{jk}=A_j^\dagger A_k,\qquad
 D_{jk}=A_j^\dagger(I-KK^\dagger)A_k
        =Q_{jk}-V^\dagger Q_{jk}V.
\tag{216.4}
```

$`KK^\dagger\le I`$ 保证由 $`D_{jk}`$ 组成的块矩阵半正定；由（216.3）还有

```math
\sum_jD_{jj}=I-V^\dagger V=|f\rangle\langle f|.
\tag{216.5}
```

若 $`y\perp f`$，则所有非负数 $`\langle A_jy,(I-KK^\dagger)A_jy\rangle`$ 的和为零，所以 $`(I-KK^\dagger)^{1/2}A_jy=0`$ 对每个 $`j`$ 成立。这同时消去每个交叉块在 $`f^\perp`$ 上的行与列。因此存在一个半正定标量矩阵 $`C=(c_{jk})`$，使

```math
D_{jk}=c_{jk}|f\rangle\langle f|,
 \qquad Q_{jk}-V^\dagger Q_{jk}V=c_{jk}|f\rangle\langle f|.
\tag{216.6}
```

下面使用有限维 Stein 方程的经典 Gramian 迭代；稳定情形的级数及唯一性见 Pontes Duff、Kürschner，*Numerical computation and new output bounds for time-limited balanced truncation of discrete-time systems*，arXiv:1902.01652v1，式（4b）、（5b）。这里所需的复矩阵版本直接由以下望远镜恒等式给出。若 $`h\ne h_c`$，定理214.2和第213.18式保证 $`V`$ 的三个特征值模均小于一，故 $`V^n\to0`$。迭代（216.6）并取极限，得到

```math
Q_{jk}=c_{jk}\sum_{n=0}^{\infty}(V^\dagger)^n
                   |f\rangle\langle f|V^n=c_{jk}I_3.
\tag{216.7}
```

最后一式也可将 $`|f\rangle\langle f|=I-V^\dagger V`$ 代入有限和后望远镜消去取得。将（216.7）在 $`\psi_0`$ 上取矩阵元，由（216.3）及谱向量的正交性得
$`c_{jk}=p_j\delta_{jk}`$。所以 $`A_j/\sqrt{p_j}`$ 是等距，各自像空间两两正交，并由交织关系保持于 $`K^\dagger`$。这证明 $`3r`$ 的下界及不变块结论。

现在设 $`h=h_c`$。此时 $`0<a<1/2`$，三个特征值为 $`0,2a,-1`$。单位模特征向量属于压缩算子的约化子空间。直接代入第211.17式可取其单位向量及投影为

```math
z_- =\frac{(1,-2\sqrt{a(1+a)},0)^{\mathsf T}}{1+2a},
 \qquad Z=|z_-\rangle\langle z_-|,\qquad R=I-Z.
\tag{216.8}
```

$`VZ=ZV=-Z`$，$`V|_{\operatorname{ran}R}`$ 严格稳定，且 $`f\in\operatorname{ran}R`$。在 $`R\oplus Z`$ 分块中求解（216.6）：稳定块仍由迭代唯一给出 $`c_{jk}R`$；两个交叉块的齐次方程经迭代趋零；单位块没有强迫项。因此

```math
Q_{jk}=c_{jk}R+d_{jk}Z.
\tag{216.9}
```

在 $`R`$ 中取单位向量检验交叉 Gram 矩阵，可知 $`C=(c_{jk})`$ 半正定；在 $`Z`$ 中同样得到 $`D=(d_{jk})\ge0`$。由 $`\sum_jQ_{jj}=I`$ 得 $`\operatorname{Tr}C=\operatorname{Tr}D=1`$，所以两者秩均至少为一。又有

```math
w=\langle\psi_0,Z\psi_0\rangle=\frac a{1+2a}>0,
 \qquad v=1-w=\frac{1+a}{1+2a}>0,
 \qquad vC+wD=\operatorname{diag}(p_1,\ldots,p_r).
\tag{216.10}
```

令 $`c=\operatorname{rank}C`$、$`d=\operatorname{rank}D`$。右侧满秩，故 $`r\le c+d`$。另一方面，所有 $`A_j`$ 合成的映射 $`\bigoplus_j\mathbb C^3\to\mathcal H`$ 的 Gram 矩阵为 $`C\otimes R+D\otimes Z`$，其秩为 $`2c+d`$。于是

```math
\dim\mathcal H\ge2c+d\ge r+1,
 \qquad \dim\mathcal H\ge2c+d\ge3.
\tag{216.11}
```

这证明临界下界。整个推导只使用单个校准点的谱纯化与原算子的压缩性，没有增加实际程序寄存器。证毕。

**定理 216.3（尖锐秩成本的完整达到性）。** 对所有定义216.1参数，

```math
D_1(a,t;r)=D_\infty(a,t;r)=D_\omega(a,t;r)
 =\begin{cases}
 3r,&h\ne h_c,\\[0pt]
 \max\{3,r+1\},&h=h_c.
 \end{cases}
\tag{216.12}
```

达到曲线可取为全区间实解析，并使完整尖锐集合恰为 $`\{t\}`$；其在 $`t`$ 的双侧曲率极限存在并等于 $`\kappa_*(a,t)`$。

证明。 先取定理211.3的全域解析纯态曲线 $`\rho_u^0`$ 及其三维处理器。对非临界情形，固定一个 $`r`$ 维满秩密度矩阵 $`\tau`$，置

```math
\rho_u=\tau\otimes\rho_u^0,\qquad
 E=I_r\otimes P_0,\qquad K=I_r\otimes T_0.
\tag{216.13}
```

处理器忽略常值寄存器并使用原三维处理器，全输入精确性立即保留。常值张量因子不增加 SLD 信息，故其校准及全曲率与原曲线相同，名义秩为 $`r`$。程序预算维数至多 $`3r`$，下界保证实际联合支持恰为 $`3r`$。$`r=1`$ 时，此构造也覆盖临界位置并给出维数三。

设 $`h=h_c`$ 且 $`r\ge2`$。保留（216.8）的二维稳定子空间 $`\operatorname{ran}R`$，用一个 $`r-1`$ 维空间 $`\mathcal U`$ 替代原来的一维单位子空间；固定 $`\mathcal U`$ 上的满秩态 $`\tau`$。定义与参数无关的 CPTP 映射

```math
\Phi(X)=RXR\big|_{\operatorname{ran}R}
                    \ \oplus\ \operatorname{Tr}(ZX)\tau,
 \qquad \widetilde\rho_u=\Phi(\rho_u^0).
\tag{216.14}
```

完全正性来自正交块压缩和测量后准备，迹保持来自 $`R+Z=I`$。两个投影都约化 $`T_0`$；$`Z\le P_0`$ 也保证它们约化 $`P_0`$。在 $`\operatorname{ran}R\oplus\mathcal U`$ 上置

```math
T'=T_0\big|_{\operatorname{ran}R}\oplus(-I_{\mathcal U}),
 \qquad P'=P_0\big|_{\operatorname{ran}R}\oplus I_{\mathcal U}.
\tag{216.15}
```

它们满足 $`T'T'^\dagger=P'`$、$`P'T'=T'`$，且

```math
\operatorname{Tr}[\Phi(X)T']=\operatorname{Tr}(XT_0),
 \qquad\operatorname{Tr}[\Phi(X)P']=\operatorname{Tr}(XP_0).
\tag{216.16}
```

因此将 $`P',T'`$ 放入第211.18式的固定受控构造，就对 $`\widetilde\rho_u`$ 实现原来的全部目标通道。实际准备空间维数为 $`2+(r-1)=r+1`$，矩阵曲线仍实解析。

名义纯向量在 $`R,Z`$ 中的概率分别为（216.10）的 $`v,w`$，两者严格为正。故 $`\widetilde\rho_t`$ 的稳定块秩为一，单位块秩为 $`r-1`$，总秩恰为 $`r`$。固定 CPTP 映射的点态 SLD 单调性与精确读出下界给出

```math
0\le I_Q(\widetilde\rho_u)-I_r(u)
          \le I_Q(\rho_u^0)-I_r(u).
\tag{216.17}
```

右侧在 $`t`$ 为零，所以校准成立；其二阶比值极限为 $`\kappa_*`$，而定理211.2对实际混态曲线提供反向下极限界，因此新曲线也具有相同的双侧普通极限。这里没有依赖参数的额外准备标签，替代映射 $`\Phi`$ 始终固定。

构造的正谱始终只含 $`\lambda_+(h)`$：非临界时为原谱的重复，临界时为 $`2a`$。第215.2节的谱必要性及正谱签名的严格单调性排除其他尖锐点。相应维数下界还保证实际联合支持恰为声明的维数。正则性类别的包含关系与这些解析构造共同证明（216.12）。证毕。

**定理 216.4（满秩禁阻与三维混态例外）。** 任意有限维精确 $`C^1`$ 程序在尖锐校准点的态都不是其联合支持上的满秩态。若联合支持维数至多五且 $`h\ne h_c`$，则名义态必须为纯态。存在三维程序具有真正混态的尖锐点，当且仅当 $`a<1/2`$ 及临界位置 $`t=2a+4a^2-1`$；此时可能的混态秩恰为二，并且存在全域解析实现。

证明。 非临界下界 $`d\ge3r`$ 排除 $`r=d`$，并在 $`d\le5`$ 时强制 $`r=1`$。临界下界 $`d\ge r+1`$ 同样排除满秩；在 $`d=3`$ 时，混态只可能有 $`r=2`$。临界点存在的参数条件由定理214.2给出，定理216.3以三维达到该秩二情形。这里的存在是关于可选择的处理器，不声称每一个三维处理器都具有这样的校准。证毕。

<a id="entry-782"></a>

## 追加锚（本行以下为增补区）

<a id="section-217"></a>

## 217. 多点指定秩的谱重数与共同程序维数

**定义 217.1（尖锐集合上的秩轮廓）。** 固定 $`0<a<1`$、非空有限集合 $`S=\{t_1,\ldots,t_m\}\subset J_a`$ 及正整数 $`r_1,\ldots,r_m`$。令 $`D_\nu(a,S;\mathbf r)`$ 为第215节的一个固定全输入精确处理器及一条完整混态准备曲线满足

```math
S\subseteq\mathcal E_*(\rho),\qquad
\operatorname{rank}\rho_{t_i}=r_i\quad(1\le i\le m)
\tag{217.1}
```

所需的最小实际联合支持维数，其中 $`\nu=1,\infty,\omega`$ 分别要求 $`C^1`$、光滑、实解析。只指定这些态的秩，不指定其非零特征值。

记 $`h_i=(1+t_i)/2`$。若 $`0<a<1/2`$ 且 $`t_c=2a+4a^2-1\in S`$，称该指标为临界指标 $`c`$，并令 $`\varepsilon=1`$；否则令 $`\varepsilon=0`$。设 $`I`$ 为删去可能的临界指标后的指标集，定义

```math
R_* =\max\bigl(\{r_i:i\in I\}\cup\{0\}\bigr),\qquad
M_+=\sum_{i\in I}r_i,
\qquad
\Lambda_- =\{\lambda_-(h_i):i\in I\},
\qquad
M_- =\sum_{\lambda\in\Lambda_-}
                 \max\{r_i:i\in I,\ \lambda_-(h_i)=\lambda\}.
\tag{217.2}
```

空和取零。秩加权的谱维数定义为

```math
\mathcal N(a,S;\mathbf r)=
\begin{cases}
R_*+M_++M_-,&\varepsilon=0,\\[2pt]
\max\{R_*,1\}+M_++M_-+\max\{r_c,2\},&\varepsilon=1.
\end{cases}
\tag{217.3}
```

**定理 217.2（原算子的几何重数下界）。** 任意定义217.1的程序都满足

```math
\dim\mathcal H\ge\mathcal N(a,S;\mathbf r).
\tag{217.4}
```

其中 $`\mathcal H`$ 为该曲线的实际联合支持。对每个非临界指标 $`i`$，原空间算子 $`K^\dagger`$ 在 $`0,\lambda_+(h_i),\lambda_-(h_i)`$ 的几何重数均至少为 $`r_i`$。

证明。 对所有位置使用同一个固定归约算子 $`K`$。定理216.2在每个非临界位置给出 $`r_i`$ 个相互正交的三维不变块；每块限制具有三个不同特征值 $`0,\lambda_+(h_i),\lambda_-(h_i)`$，因此这三个特征空间各至少有 $`r_i`$ 个线性无关向量。不同位置所得的块不要求相互正交。零特征空间的维数至少为 $`R_*`$；正签名严格单调，故各位置的正特征值互异，其特征空间维数之和至少为 $`M_+`$；共享同一负签名的位置只要求取各自重数的最大值，得到 $`M_-`$。不同特征值的特征空间线性直和，于是无临界指标时已经得到（217.4）。这里计数的是几何重数，不假设整个 $`K^\dagger`$ 可对角化。

若存在临界指标，取第216.3式在该点的映射 $`A_j`$，令 $`\mathcal A(x_1,\ldots,x_{r_c})=\sum_jA_jx_j`$。第216.9式给出

```math
\mathcal A^\dagger\mathcal A=C\otimes R+D\otimes Z,
\qquad K^\dagger\mathcal A=\mathcal A(I\otimes V),
\qquad c_0=\operatorname{rank}C\ge1,\quad
d_0=\operatorname{rank}D\ge1,\quad c_0+d_0\ge r_c.
\tag{217.5}
```

此处 $`R,Z`$ 是临界三维模型的二维稳定投影和一维单位投影，$`V|_R`$ 的两个不同特征值为 $`0,2a`$，$`V|_Z=-1`$。对 $`V|_R`$ 的任一非零特征向量 $`y`$，映射 $`z\mapsto\mathcal A(z\otimes y)`$ 的 Gram 矩阵为 $`\|y\|^2C`$，故其像维数为 $`c_0`$，且由交织关系全部落在相应的 $`K^\dagger`$ 特征空间。对单位方向同理得到 $`d_0`$。因此 $`0,2a,-1`$ 的几何重数分别至少为 $`c_0,c_0,d_0`$。

非临界正签名不会等于 $`2a`$，非临界负签名也不会等于 $`-1`$。综合所有不同特征空间，有

```math
\dim\mathcal H\ge
\max\{R_*,c_0\}+M_++M_-+c_0+d_0
\ge\max\{R_*,1\}+M_++M_-+\max\{r_c,2\}.
\tag{217.6}
```

这正是临界分支的下界。所有向量均在原空间 $`\mathcal H`$ 中，纯化辅助空间没有计入预算。证毕。

**定理 217.3（指定秩轮廓的完整达到性）。** 对所有定义217.1参数，

```math
D_1(a,S;\mathbf r)=D_\infty(a,S;\mathbf r)
 =D_\omega(a,S;\mathbf r)=\mathcal N(a,S;\mathbf r).
\tag{217.7}
```

达到曲线可以使完整尖锐集合恰为 $`S`$，并在各 $`t_i`$ 具有等于 $`\kappa_*(a,t_i)`$ 的双侧普通曲率极限。

证明。 令 $`L=\max\{R_*,\varepsilon\}`$。由于 $`S`$ 非空，有 $`L\ge1`$。对每层 $`1\le k\le L`$，取不同实节点组成的集合

```math
\Lambda_k=\{0\}\cup
 \bigcup_{\substack{i\in I\\r_i\ge k}}
       \{\lambda_+(h_i),\lambda_-(h_i)\}
 \cup
 \begin{cases}
 \{2a\},&\varepsilon=1,\ k=1,\\[0pt]
 \varnothing,&\text{其余情形}.
 \end{cases}
\tag{217.8}
```

这些节点均在 $`(-1,1)`$ 内。对每层使用第213.21—213.22式的 Gram 构造：

```math
\langle x_{k,\lambda},x_{k,\mu}\rangle
       =\frac1{1-\lambda\mu},\qquad
V_kx_{k,\lambda}=\lambda x_{k,\lambda},\qquad
V_k^\dagger V_k=I-|q_k\rangle\langle q_k|,
\quad q_k=x_{k,0}.
\tag{217.9}
```

这是定理213.4已具体给出的规定谱部分等距工具；其经典背景仍见 Garcia、Sherman，*Matrices Similar to Partial Isometries*，arXiv:1703.02960v2，引理2及定理1。不同层取正交直和。若有临界指标，另加维数 $`d_c=\max\{1,r_c-1\}`$ 的正交单位子空间 $`\mathcal U`$，并令 $`V|_{\mathcal U}=-I`$。若无临界指标则不加该空间。置

```math
V=\bigoplus_{k=1}^{L}V_k\ \oplus\ (-I_{\mathcal U}),
\qquad T=V^\dagger,\qquad P=V^\dagger V.
\tag{217.10}
```

不存在的末块省略。$`P`$ 是投影，且 $`TT^\dagger=P`$、$`PT=T`$，故第211.18式给出一个固定受控 CPTP 处理器。

先数维数。每个非临界正签名出现在前 $`r_i`$ 层；每个负签名出现在以该纤维最大秩为层数的前若干层；每层都有一个零节点。若有临界指标，另有第一层的一个 $`2a`$ 节点以及 $`d_c`$ 个单位方向。因此

```math
\dim\mathcal H
=L+M_++M_-+\varepsilon(1+d_c)
=\mathcal N(a,S;\mathbf r),
\tag{217.11}
```

其中无临界指标时把最后一项解释为零。

对每个非临界指标 $`i`$，其三个规范特征值都出现在第 $`1,\ldots,r_i`$ 层。第213.24—213.25式的归一化特征向量 Gram 恒等式给出等距映射 $`U_{ik}`$，把第211节的规范三维模型嵌入各层，并满足

```math
U_{ik}^\dagger P U_{ik}=P_0,\qquad
VU_{ik}=U_{ik}T_0(a,t_i)^\dagger,\qquad
U_{ik}^\dagger T U_{ik}=T_0(a,t_i).
\tag{217.12}
```

令 $`\rho_i^0(u)`$ 为相应的全域解析规范纯态曲线，选常值严格正权重 $`p_{ik}`$，使 $`\sum_{k=1}^{r_i}p_{ik}=1`$，并置

```math
\sigma_i(u)=\sum_{k=1}^{r_i}
 p_{ik}U_{ik}\rho_i^0(u)U_{ik}^\dagger.
\tag{217.13}
```

各像空间位于正交的层中，所以曲线秩为 $`r_i`$；常值正交块权重没有额外 Fisher 项，其点态 SLD 信息等于规范纯曲线的信息。各块都满足精确的 $`P,T`$ 期望约束，因此它在同一个处理器中全区间、全输入精确，并在 $`t_i`$ 保留最优曲率。

若有临界指标，其二维稳定模型的谱为 $`\{0,2a\}`$、缺陷为 $`|f\rangle\langle f|`$。对这两个特征向量使用同一 Gram 恒等式，便把该稳定模型等距嵌入第一层的 $`\{0,2a\}`$ 不变子空间。若 $`r_c=1`$，将它与 $`\mathcal U`$ 中的一个单位方向一起嵌入，就得到完整规范纯曲线。若 $`r_c\ge2`$，在 $`\mathcal U`$ 上选满秩态，使用第216.14式的固定压缩与替代映射。该映射保留两个所需矩，给出名义秩恰为 $`r_c`$ 的解析曲线 $`\sigma_c`$；定理216.3的点态 SLD 单调性及上下界夹逼保留其最优普通曲率极限。此构造使用 $`d_c=r_c-1`$ 个单位方向。

现在所有 $`\sigma_i`$ 都在同一个上述空间和处理器中。取 Lagrange 多项式及三次振幅

```math
L_i(u)=\prod_{j\ne i}\frac{u-t_j}{t_i-t_j},\qquad
g_i(u)=\frac{L_i(u)^3}{\sqrt{\sum_jL_j(u)^6}},\qquad
\rho_u=\sum_i g_i(u)^2\sigma_i(u).
\tag{217.14}
```

分母在实轴恒正，因为 $`\sum_iL_i=1`$。因此 $`\rho`$ 在整个 $`J_a`$ 上实解析，并由矩约束的线性保持全输入精确性。各节点满足 $`\rho_{t_i}=\sigma_i(t_i)`$ 及 $`\rho'_{t_i}=\sigma_i'(t_i)`$，故全部指定秩及点态 SLD 校准都精确达到。

参数相关混合的信息上界及零权重处理沿用定理215.3。每个分支的信息局部有界：非临界分支与规范纯曲线相同，临界分支由固定 CPTP 映射的数据处理界控制。在 $`t_i`$ 附近，其余权重为 $`O((u-t_i)^6)`$，振幅导数平方之和为 $`O((u-t_i)^4)`$，从而

```math
I_Q(\rho_u)-I_r(u)
\le g_i(u)^2\bigl(I_Q(\sigma_i(u))-I_r(u)\bigr)
       +O((u-t_i)^4).
\tag{217.15}
```

结合通用曲率下界，得到每个指定点的双侧普通极限等于 $`\kappa_*`$。这使用实际准备态的信息上界，没有把一个未保留的标签当作实际信息量。

构造中 $`K^\dagger=V`$ 的正谱恰为 $`\{\lambda_+(h_i):1\le i\le m\}`$。第215.2节的谱必要性与正签名严格单调性排除所有其他尖锐点，所以完整尖锐集合恰为 $`S`$。构造的实际联合支持若低于（217.11），便与定理217.2矛盾，故其实际维数也等于 $`\mathcal N`$。解析构造、正则性类别包含关系及统一下界共同证明（217.7）。证毕。

<a id="entry-784"></a>

## 追加锚（本行以下为增补区）

<a id="section-218"></a>

## 218. 同一五维纯态曲线的三个尖锐点

**定义 218.1（三重负谱的五维实处理器）。** 固定 $`a=1/10`$、$`r_0=19/20`$。令 $`h_1<h_2<h_3`$ 为

```math
16000000h^3-16056900h^2+3496569h-208012=0
\tag{218.1}
```

在 $`(104/1000,105/1000)`$、$`(171/1000,172/1000)`$、$`(727/1000,729/1000)`$ 中的三个根，置 $`t_i=2h_i-1`$、$`S=\{t_1,t_2,t_3\}`$。三个隔离区间都满足 $`h_i(r_0+2a)-a>0`$，所以定理214.2的未平方符号条件给出 $`\lambda_-(h_i)=-r_0`$。采用定理213.4的五维实 Gram 处理器，记

```math
V=T^\dagger,\qquad V^\dagger V=P=I-|q\rangle\langle q|,
\qquad \|q\|=1,\quad Vq=0,
\qquad \operatorname{spec}V=
\{0,-r_0,\lambda_+(h_1),\lambda_+(h_2),\lambda_+(h_3)\}.
\tag{218.2}
```

**定理 218.2（三个尖锐点的最小纯态维数达到）。** 定义218.1的同一个五维处理器具有一条在整个 $`J_a`$ 上实解析的纯态准备曲线，对所有信号输入精确实现目标通道，其完整尖锐集合恰为 $`S`$，且三个尖锐点的双侧普通曲率极限均等于各自的 $`\kappa_*`$。因此，按定义213.1的纯态维数，

```math
d_1(a,S)=d_\infty(a,S)=d_\omega(a,S)=5.
\tag{218.3}
```

证明。 谱必要性已经给出五维下界。下面在（218.2）的固定处理器中构造一条纯态曲线。

先把参数写成 $`p=(1+u)/2\in(a,1)`$，令 $`\mathcal P=\operatorname{ran}P`$，这是四维实空间。所有形如

```math
\psi(p)=\sqrt p\,v(p)+\sqrt{1-p}\,q,\qquad
v(p)\in\mathcal P,\quad \|v(p)\|=1
\tag{218.4}
```

的向量都精确具有所需的 $`P`$ 期望。置

```math
A=\frac12\bigl(PTP+(PTP)^\dagger\bigr)\big|_{\mathcal P},
\qquad w=Tq,\qquad
\phi_p(v)=p\langle v,Av\rangle+\sqrt{p(1-p)}\langle w,v\rangle.
\tag{218.5}
```

由于所有向量和矩阵都取实值，剩下的完整通道约束就是 $`\phi_p(v)=a`$。

下面先证明在 $`a<p\le1/5`$ 时，这个球面水平集是连通的光滑二维球面。所需的四维谱数据可以完全在有理数域确定。三个正特征值是

```math
x^3-\frac{3617}{2660}x^2+\frac{12017}{26600}x-\frac{43}{1330}=0
\tag{218.6}
```

的根；这由 $`\lambda_+(h)=[h(r_0+2a)-a]/(h+ar_0)`$ 代入（218.1）得到。令 $`C`$ 为首一多项式

```math
p_V(x)=x^5-\frac{109}{266}x^4-\frac{44689}{53200}x^3
             +\frac{211123}{532000}x^2-\frac{43}{1400}x
\tag{218.7}
```

的伴随矩阵，采用次对角线为一、末列为负系数的约定。取 $`f=e_5`$。该稳定可观测对具有唯一正定有理 Gram 矩阵
$`G-C^{\mathsf T}GC=ff^{\mathsf T}`$。将 $`\ker C`$ 的向量 $`q`$ 归一化为 $`f^{\mathsf T}q=1`$，便有 $`Gq=f`$。以 $`G`$ 为内积，此时 $`\|q\|_G=1`$，$`V=C`$、$`T=G^{-1}C^{\mathsf T}G`$、$`P=I-qf^{\mathsf T}`$ 给出（218.2）的一个实模型。归一化特征向量的 Gram 恒等式将它与定义218.1的模型等距对应。

在 $`q^\perp=\{x:x_5=0\}`$ 上计算（218.5），所得 $`A`$ 的首一特征多项式及 $`w`$ 的标量预解式为

```math
\chi(z)=z^4-\frac{109}{266}z^3
 -\frac{3193264889}{2830240000}z^2
 +\frac{22257060291}{56604800000}z
 +\frac{742355953371}{4528384000000},
\qquad
\langle w,(zI-A)^{-1}w\rangle=\frac{N(z)}{\chi(z)},
\tag{218.8}
```

其中

```math
N(z)=\frac{1958151}{1960000}z^3
 -\frac{296121711}{744800000}z^2
 -\frac{1052658255129}{1132096000000}z
 +\frac{8261046873}{22641920000}.
\tag{218.9}
```

这些恒等式只涉及上述有理 Stein 方程与四维行列式。对 $`\chi`$ 作 Sturm 计数，再在下列有理隔离区间上代入 $`N/\chi'`$，得到其四个不同实根 $`\alpha_j`$ 及 $`w`$ 在相应正交归一特征向量上的坐标 $`\beta_j`$ 的界：

| $`j`$ | $`\alpha_j`$ 的隔离区间 | $`|\beta_j|`$ 的严格下界 |
| --- | --- | --- |
| $`1`$ | $`(-23653/24168,-7670/7837)`$ | $`13/100`$ |
| $`2`$ | $`(-3426/13351,-2339/9115)`$ | $`82/100`$ |
| $`3`$ | $`(11035/16514,6449/9651)`$ | $`53/100`$ |
| $`4`$ | $`(9074/9289,16291/16677)`$ | $`10/100`$ |

这里 $`\beta_j^2=N(\alpha_j)/\chi'(\alpha_j)`$，故这些界是有理多项式不等式的结果。相邻根的间距还分别严格小于 $`73/100,93/100,31/100`$。

记 $`z_p=\sqrt{p(1-p)}`$。球面上的临界向量满足 $`2pAv+z_pw=2\nu v`$。由于 $`\beta_j\ne0`$，临界乘子不等于任何 $`p\alpha_j`$，消去向量后恰为

```math
\frac{z_p^2}{4}\sum_{j=1}^4
       \frac{\beta_j^2}{(\nu-p\alpha_j)^2}=1.
\tag{218.10}
```

在相邻两个极点之间，Cauchy–Schwarz 不等式给出左侧的下界

```math
\frac{1-p}{4p}
 \left(\frac{|\beta_j|+|\beta_{j+1}|}
                  {\alpha_{j+1}-\alpha_j}\right)^2>1
\qquad(a<p\le1/5).
\tag{218.11}
```

第一因子至少为一，第二因子的分子下界分别为 $`95/100,135/100,63/100`$，严格大于相应分母上界。因此内部三个极点区间没有临界乘子。两个外部区间的左侧各自严格单调地从零变到无穷，故各有一个乘子。外部乘子使球面 Hessian 分别正定和负定，所以 $`\phi_p`$ 恰有一个非退化极小点和一个非退化极大点。

第211节的任何嵌入规范分支都在该水平上给出正则点：其角度根的导数不为零。因此 $`a`$ 严格介于最小值和最大值之间。以 $`\nabla\phi_p/\|\nabla\phi_p\|^2`$ 的流连接各个正则水平，紧性保证在任意闭的正则值区间内可继续；从非退化极小点附近的二维球面出发，得到整个目标水平集都为一个光滑二维球面。特别地，它连通，且作为正则代数水平集是 Nash 流形。

令 $`v_i(p)`$ 为三个分别尖锐的规范分支在（218.4）中的单位向量。它们在整个 $`(a,1)`$ 上都是正则 Nash 分支。这里无需角度本身为半代数函数：以半角正切替换第211节的三角函数，向量坐标由固定区间内唯一选定的代数根给出；非零根导数使这些半代数坐标实解析。

现在在 $`p=13/100`$ 附近把第一分支连接到第二分支，在 $`p=19/100`$ 附近把第二分支连接到第三分支。这两个位置分别位于 $`(h_1,h_2)`$ 与 $`(h_2,h_3)`$，且小于 $`1/5`$。每个过渡水平集连通，因此两端可由一条 $`C^4`$ 半代数路径连接；这可在有限个 Nash 坐标图中用端点四阶平坦的多项式重参数拼接得到。

为使连接同时适用于附近参数，设 $`\gamma(s)`$ 是过渡位置 $`p_0`$ 的路径，端点为 $`v_i(p_0),v_{i+1}(p_0)`$。先将

```math
\gamma(s)+(1-s)\bigl(v_i(p)-v_i(p_0)\bigr)
           +s\bigl(v_{i+1}(p)-v_{i+1}(p_0)\bigr)
\tag{218.12}
```

归一化到单位球面，再沿 $`\phi_{p_0}`$ 的球面梯度作一个标量修正。该梯度在紧路径上处处非零，隐函数定理给出统一的小参数邻域及唯一 $`C^4`$ 半代数修正。两个端点本来已满足精确约束，所以其修正恒为零。用端点前四阶导数均为零的多项式过渡参数，便得到一条全区间 $`C^4`$ 半代数正则截面 $`s_0(p)=(p,v_0(p))`$，在每个 $`h_i`$ 的邻域与相应规范分支完全相同。

最后将此截面解析化，同时保留指定二阶导数。换用闭区间坐标

```math
x=\sqrt{1-p},\qquad 0\le x\le\sqrt{9/10},\qquad
F(x,v)=(1-x^2)\langle v,Av\rangle
             +x\sqrt{1-x^2}\langle w,v\rangle-a.
\tag{218.13}
```

此函数在闭区间的一个开邻域中实解析。两个端点所用的规范分支也在该坐标中解析延拓：第211.30式的严格夹逼在 $`p=a,1`$ 仍成立；第211.32—211.33式的根导数论证在 $`p=a`$ 原样适用，在 $`p=1`$ 去掉含平方根的项后仍给出严格正角导数。将 $`\sqrt{1-p}`$ 替换为 $`x`$ 后，解析隐函数定理便同时覆盖两个端点。因此 $`v_0`$ 在此闭区间上是一个正则 $`C^4`$ 半代数截面，并在两端邻域解析。沿这两个端点分支向外延伸，还得到闭区间开邻域上的 $`C^4`$ 半代数延拓。

Carbone、Fernando，*Nash approximation of differentiable semialgebraic maps*，arXiv:2601.13164v1，定理1.1，在紧半代数区间、Euclidean 目标和 $`\mu=2`$ 的情形提供任意接近 $`v_0`$ 的 $`C^2`$ Nash 逼近。再作有限 Hermite 多项式修正，令逼近在三个标记点的二阶数据精确匹配。修正的 $`C^2`$ 范数受这些有限个逼近误差的常数倍控制，故得到的 Nash 向量 $`Y(x)`$ 仍可任意 $`C^2`$ 接近 $`v_0`$，并在闭区间的开邻域实解析。

令 $`y=Y/\|Y\|`$，并取球面切向梯度 $`g=(I-yy^{\mathsf T})\nabla_vF(x,y)`$。由于原截面在紧区间上正则，足够接近的逼近使 $`\|g\|`$ 有严格正的统一下界。设

```math
\widehat v(x)=
\frac{y(x)+\tau(x)g(x)}
     {\sqrt{1+\tau(x)^2\|g(x)\|^2}},\qquad
F(x,\widehat v(x))=0.
\tag{218.14}
```

在 $`\tau=0`$ 时，末式左侧对 $`\tau`$ 的导数为 $`\|g\|^2`$。紧性给出一个统一的小 $`\tau`$ 区间，导数始终为正；先固定足够小的区间，再把逼近取得足够接近，就使两端函数值异号。因此每个 $`x`$ 都有唯一小根。解析隐函数及唯一性把这些根接成闭区间某个开邻域上的同一解析函数 $`\tau`$。

在三个标记点，归一化保持与单位截面 $`v_0`$ 的二阶数据一致，所以 $`F(x,y(x))`$ 的二阶数据全为零。对隐式方程逐次求导，得到

```math
\tau=\tau'=\tau''=0
\quad\text{在每个标记点成立}.
\tag{218.15}
```

因而 $`\widehat v`$ 精确保留三个规范分支的二阶数据，同时单位范数与矩约束恒等成立。由 $`x=\sqrt{1-p}`$ 在三个内部节点附近解析且导数非零，回到 $`p`$ 或 $`u`$ 后仍保留相应二阶数据。

把 $`\widehat v`$ 代入（218.4），便得到全区间实解析纯态准备。两个矩约束使固定处理器对每个信号矩阵单位都精确。在实规范中，准备信息满足

```math
I_Q(\psi_u)-I_r(u)=4p\left\|\frac{d\widehat v}{du}\right\|^2.
\tag{218.16}
```

规范分支在其指定点的一阶导数为零，二阶导数给出最优曲率。构造保留这些二阶数据，故同时保留三个点的校准及双侧普通曲率极限。正谱只包含 $`S`$ 的三个正签名，谱必要性和严格单调性排除额外尖锐点。五维下界还保证实际联合支持恰为五维，完成（218.3）。证毕。

<a id="entry-786"></a>

## 追加锚（本行以下为增补区）

<a id="section-219"></a>

## 219. 非临界聚簇的最小纯态实现与高参数精确容量

**定义 219.1（实精确纤维与正交移位坐标）。** 固定第213节的有限集合 $S$，取其共同处理器 $V=T^{\mathsf T}$、$P=V^{\mathsf T}V=I-qq^{\mathsf T}$，并置 $H=(T+T^{\mathsf T})/2$。对 $a<p<1$，定义

$$
Y_p=\{\psi\in S^{N-1}:
 \psi^{\mathsf T}(P-pI)\psi=0,\quad
 \psi^{\mathsf T}(H-aI)\psi=0\},
\qquad
Y_p^+=\{\psi\in Y_p:q^{\mathsf T}\psi>0\}.
\tag{219.1}
$$

这里球面与矩阵均取实数。由于 $|q^{\mathsf T}\psi|=\sqrt{1-p}>0$，$Y_p$ 是 $Y_p^+$ 与其反足像的不交并；映射
$\psi=\sqrt p\,v+\sqrt{1-p}\,q$ 把 $Y_p^+$ 等同于第218节的单位向量矩约束纤维。

当谱节点为互异的 $0,\lambda_1,\ldots,\lambda_{N-1}\in(-1,1)$ 时，可用以下正交坐标实现同一处理器：

$$
V_1=(0),\quad z_1=(1),\qquad
V_{j+1}=
\begin{pmatrix}
 V_j&\sqrt{1-\lambda_j^2}\,z_j\\[0pt]
 0&\lambda_j
\end{pmatrix},
\qquad
z_{j+1}=
\binom{-\lambda_jz_j}{\sqrt{1-\lambda_j^2}}.
\tag{219.2}
$$

**定理 219.2（任意非临界中心附近的最小纯态实现）。** 固定 $0<a<1$、整数 $m\ge2$ 及

$$
h_0\in(a,1),\qquad h_0\ne a+2a^2.
\tag{219.3}
$$

存在 $\delta>0$，使得对任意互异节点
$a<h_1<\cdots<h_m<1$、$|h_i-h_0|<\delta$，置
$S=\{2h_i-1:1\le i\le m\}$，第213.4节的同一个共同处理器就具有一条全区间、全输入精确的实解析实纯态准备曲线。其完整尖锐集合恰为 $S$，各点的双侧普通曲率极限均为 $\kappa_*(a,2h_i-1)$，且

$$
d_1(a,S)=d_\infty(a,S)=d_\omega(a,S)=N(a,S).
\tag{219.4}
$$

此处允许不同节点具有相同的负谱签名；邻域半径依赖于 $a,h_0,m$。

证明。 先核对（219.2）的坐标。归纳给出 $\|z_j\|=1$、$V_j^{\mathsf T}z_j=0$，以及

$$
V_j^{\mathsf T}V_j=\operatorname{diag}(0,1,\ldots,1).
\tag{219.5}
$$

因此 $q=e_1$。对任一稳定特征向量 $Vx_\lambda=\lambda x_\lambda$，若 $q^{\mathsf T}x_\lambda=0$，则（219.5）给出 $\|Vx_\lambda\|=\|x_\lambda\|$，与 $|\lambda|<1$ 矛盾。将其归一化为 $q^{\mathsf T}x_\lambda=1$，便有

$$
(1-\lambda\mu)x_\lambda^{\mathsf T}x_\mu=1,
\qquad
x_\lambda=(I-\lambda V^{\mathsf T})^{-1}q.
\tag{219.6}
$$

第一式来自（219.5）；第二式来自
$V^{\mathsf T}Vx_\lambda=x_\lambda-q=\lambda V^{\mathsf T}x_\lambda$，且 $\|V\|\le1$ 使逆矩阵存在。第一式与第213.21式的 Gram 矩阵相同，故（219.2）与原共同处理器由固定正交变换对应。第二式保证归一化特征向量在稳定谱节点合并时仍有连续极限；无需对全部特征向量的退化 Gram 矩阵取逆。

令 $k$ 为这些节点的不同负签名数，先固定 $1\le k\le m$。按先正后负的次序将全部不同非零谱节点放入（219.2）。当全部 $h_i\to h_0$ 时，$N=1+m+k$ 维矩阵连续趋于一个矩阵 $V_*^{(k)}$，其对角谱为

$$
0,\quad\underbrace{\lambda_+(h_0),\ldots,\lambda_+(h_0)}_{m\text{ 个}},
\quad\underbrace{\lambda_-(h_0),\ldots,\lambda_-(h_0)}_{k\text{ 个}}.
\tag{219.7}
$$

由非临界条件和第213.18式，两种非零极限签名都严格位于单位圆内，且与零两两不同。式（219.6）的逆矩阵在这些极限附近连续。因此每个三维规范子空间的三个生成向量
$q,x_{\lambda_+(h_i)},x_{\lambda_-(h_i)}$ 趋于同一组三个线性无关向量；其三乘三 Gram 矩阵始终趋于由三个不同稳定节点给出的正定矩阵。较大矩阵中重复特征值的存在不破坏这组三向量的独立性。

更明确地，在第211节的三维模型 $V_i=T_0(a,2h_i-1)^{\mathsf T}$ 中，将零特征向量取为 $f$，另外两个特征向量取 $f^{\mathsf T}y_\lambda=1$ 的规范。记它们组成的可逆矩阵为
$Y_i=(f,y_{\lambda_+(h_i)},y_{\lambda_-(h_i)})$，共同处理器中的对应矩阵为
$X_i=(q,x_{\lambda_+(h_i)},x_{\lambda_-(h_i)})$。两组三向量具有相同 Gram 矩阵，所以

$$
U_i=X_iY_i^{-1},\qquad U_i^{\mathsf T}U_i=I_3
\tag{219.8}
$$

就是第213.25式的等距嵌入。局部三维模型的三个特征值始终分离，$Y_i$ 及其逆矩阵连续；故所有 $U_i$ 趋于同一个等距嵌入 $U_*^{(k)}$。

第211节规范准备的角度方程在 $p=h=h_0$ 有根 $\Theta=0$，角导数严格为正。其隐式根随 $p,h$ 在这个点附近实解析。因此各嵌入规范准备 $\psi_i(p)$ 在 $p,h_i\to h_0$ 时都趋于同一个单位向量 $\psi_*^{(k)}$。

在正规范中写
$\psi=\sqrt p\,v+\sqrt{1-p}\,q$，其中 $v\in q^\perp$、$\|v\|=1$。置

$$
A=PHP|_{q^\perp},\qquad w=PTq,\qquad
F(p,v)=p\,v^{\mathsf T}Av+\sqrt{p(1-p)}\,w^{\mathsf T}v-a.
\tag{219.9}
$$

因 $T^{\mathsf T}q=Vq=0$，$F=0$ 恰为剩余的实矩约束。上述严格正角导数是一条球面切向导数，所以在极限向量 $v_*^{(k)}$ 处，$\nabla_{S^{N-2}}F(h_0,v_*^{(k)})\ne0$。

选一个包含该点的球面 Nash 坐标图，并以这个非零导数方向作为待解坐标。带矩阵系数参数的隐函数定理将附近的精确纤维写成

$$
v=\Phi(p,z;V),\qquad z\in B\subset\mathbb R^{N-3},
\tag{219.10}
$$

其中 $B$ 可取开球，$\Phi$ 为正则 Nash 图。将参数邻域缩小后，所有附近规范分支在所需的 $p$ 区间内都落在对应于一个较小同心球的图内。这里也可把矩阵系数当作独立实参数应用隐函数定理，再限制回（219.2）的实际处理器。对每个 $k$ 分别取得这样的邻域，最后在有限个 $k=1,\ldots,m$ 中取最小半径，便统一处理负签名发生相等或分离的情况。

现在取 $p_i=(h_i+h_{i+1})/2$，并在各 $p_i$ 附近选互不相交、避开所有 $h_j$ 的过渡区间。在图（219.10）的自由坐标中，用取值于 $[0,1]$、两端前四阶导数为零的多项式过渡参数，对第 $i$ 与第 $i+1$ 条规范分支作凸组合。较小球的凸性保证整段仍在图内；代回 $\Phi$ 后，矩约束始终精确，球面梯度始终非零。各区间之外沿用对应规范分支，从而得到全区间 $C^4$ 半代数正则截面，在每个 $h_i$ 附近恰等于第 $i$ 条规范分支，在两端分别采用第一条和最后一条分支。这里仅使用所选局部图的连通性，不要求完整纤维连通。

将第218.13—218.15式的解析化论证应用于此截面。具体地，$x=\sqrt{1-p}$ 把区间紧化为 $[0,\sqrt{1-a}]$，第211.30—211.33式保证两端规范分支在该坐标下解析且正则。Carbone–Fernando，*Nash approximation of differentiable semialgebraic maps*，arXiv:2601.13164v1，定理1.1在 Euclidean 目标下给出 $C^2$ Nash 逼近。有限 Hermite 修正匹配全部 $m$ 个节点的二阶数据；归一化后，沿球面切向梯度的统一标量解析修正恢复 $F=0$。该修正参数在每个节点的值、一阶和二阶导数均为零。因此所得解析纯态曲线精确保留所有规范尖锐二阶数据。

恒等式 $I_Q-I_r=4p\|dv/du\|^2$ 给出各点的最优双侧普通曲率极限；两个精确矩给出固定处理器的全输入精确性。正签名严格单调，而处理器正谱恰含所选的 $m$ 个正签名，故没有额外尖锐点。第213节的原空间谱必要性给出 $N(a,S)$ 维下界，并迫使实际联合支持达到这一维数。这证明（219.4）。证毕。

**定理 219.3（高参数区域单条纯态曲线的精确容量）。** 固定 $1/2\le a<1$ 与整数 $d\ge3$。在实际联合支持维数不超过 $d$ 的全区间、全输入精确固定程序中，令 $\mathcal C^{\mathrm{pure}}_\nu(a;d)$ 为单条纯态准备曲线的完整尖锐集合基数的最大值，其中 $\nu=1,\infty,\omega$ 分别表示 $C^1$、光滑与实解析。则

$$
\mathcal C^{\mathrm{pure}}_1(a;d)
=\mathcal C^{\mathrm{pure}}_\infty(a;d)
=\mathcal C^{\mathrm{pure}}_\omega(a;d)
=\left\lfloor\frac{d-1}{2}\right\rfloor.
\tag{219.11}
$$

证明。 在 $a\ge1/2$ 时，正、负谱签名各自对尖锐位置单射。因此任意 $m$ 个不同尖锐点都强制 $1+2m$ 个不同谱值，第213节的原空间谱必要性给出 $m\le\lfloor(d-1)/2\rfloor$。这个有限上界也排除无限尖锐集合。

取 $m=\lfloor(d-1)/2\rfloor$。若 $m=1$，使用第211节的全域解析规范纯态曲线。若 $m\ge2$，任选 $h_0\in(a,1)$。由于 $a+2a^2\ge1$，该中心自动非临界。定理219.2允许在其邻域任选 $m$ 个互异节点，并给出一条实际支持维数 $N=2m+1\le d$ 的解析实纯态曲线，其完整尖锐集合恰有 $m$ 个元素。解析类包含于其余两个正则性类，故三个最大值均达到上界。这个容量结论选择了位置集合，不宣称每个预先指定的、彼此远离的有限集合都已经达到最小纯态维数。证毕。

**定理 219.4（同族处理器的正则实纤维可以断连）。** 令

$$
a=\frac12,\qquad
\frac12<h_1<h_2\le\frac12+2\cdot10^{-12},\qquad
p=\frac{99}{100}.
\tag{219.12}
$$

第213.4节的五维共同处理器在此 $p$ 的实精确纤维处处正则，但 $Y_p^+$ 恰有两个连通分支。

证明。 先给出对整个（219.12）范围有效的扰动界。若 $h=1/2+e$、$0<e\le2\cdot10^{-12}$，第213.2式的量满足

$$
b(h)^2=\frac{e+e^2}{1/4+e}<\left(\frac3{10^6}\right)^2,
\qquad |s(h)|<\frac4{10^6}.
\tag{219.13}
$$

两个谱根的模不超过正方程 $x^2-|s(h)|x-b(h)=0$ 的正根。将 $x=1/500$ 代入后严格为正，所以四个非零谱节点均满足 $|\lambda_j|<\delta=1/500$。

在（219.2）的坐标中，$V$ 的对角线误差不超过 $\delta$，第一上副对角线误差不超过 $\delta^2$，更远的上三角项依次不超过 $\delta,\delta^2,\ldots$。分别取行和、列和，再用
$\|B\|_2\le\sqrt{\|B\|_1\|B\|_\infty}$，得到

$$
\|H-H_0\|_2\le\|V-J_5\|_2
\le\delta+\delta^2+\frac{\delta}{1-\delta}
=\frac{499999}{124750000}<\frac1{125},
\qquad H_0=\frac{J_5+J_5^{\mathsf T}}2.
\tag{219.14}
$$

考虑有理参考矩阵束

$$
M_0(\xi)=H_0-\frac12I+
\xi\operatorname{diag}\left(-\frac{99}{100},
 \frac1{100},\frac1{100},\frac1{100},\frac1{100}\right).
\tag{219.15}
$$

有理惯性与逆矩阵计算给出：

| $\xi$ | $i_+(M_0(\xi))$ | $\|M_0(\xi)^{-1}\|_\infty$ |
| --- | --- | --- |
| $-40$ | $1$ | $1395685/110344$ |
| $-10$ | $2$ | $227720/37663$ |
| $5$ | $1$ | $7105180/736451$ |
| $50$ | $2$ | $203/50$ |
| $100$ | $3$ | $6$ |
| $150$ | $4$ | $4480/747$ |

这些矩阵均对称可逆，表中逆范数都严格小于 $13$。因此（219.14）的小扰动保持所有六个矩阵的惯性：沿扰动线段，逆矩阵范数与扰动范数的乘积小于 $13/125<1$，不会经过奇异矩阵。

实际矩阵束 $M(\xi)=H-aI+\xi(P-pI)$ 的惯性在这六个参数依次为 $1,2,1,2,3,4$。每两个相邻参数之间都必须有一个行列式零点。行列式只有五次，所以恰有五个互异实单根，且没有其他根。其完整实轴惯性顺序由这五次穿越唯一确定；在两端分别为一与四。

置 $Q(\theta)=\cos\theta(P-pI)+\sin\theta(H-aI)$ 及
$\Omega^j=\{\theta\in S^1:i_+(Q(\theta))\ge j\}$。上半圆满足
$Q(\theta)=\sin\theta\,M(\cot\theta)$，下半圆满足
$Q(\theta+\pi)=-Q(\theta)$。将两段惯性顺序拼合，得到 $\Omega^4$ 恰有两个弧分支，它们均包含于 $\Omega^3$ 的同一个弧分支中；$\Omega^3$ 本身连通，$\Omega^5=\varnothing$。两弧嵌入一弧的相对一阶 Betti 数为一。

此处使用 Lerario，*Convex pencils of real quadratic forms*，arXiv:1106.4678v3，定理18的球面版本：对两个齐次实二次型的共同零点集 $Y\subset S^n$，取零锥及 $\mathbb Z_2$ 同调系数，在 $j<n-2$ 时有

$$
\widetilde b_j(Y)=b_0(\Omega^{n-j},\Omega^{n-j+1})
+b_1(\Omega^{n-j-1},\Omega^{n-j}).
\tag{219.16}
$$

这里 $n=4$、$j=0<2$，所以该公式给出

$$
\widetilde b_0(Y_p)=2+1=3,\qquad
b_0(Y_p)=4,\qquad b_0(Y_p^+)=2.
\tag{219.17}
$$

实单根还给出正则性。若共同零点奇异，则某个 $M(\xi)$ 的核向量同时满足
$x^{\mathsf T}(P-pI)x=0$；这会使其零特征值对 $\xi$ 的导数为零，令行列式根不再简单，矛盾。$\sin\theta=0$ 的两点仍可逆。

最后，固定内部中心 $h_0=1/2+10^{-12}$，并在定理219.2给出的邻域内选两个互异节点，同时使它们满足（219.12）。同一处理器便既有达到全部指定尖锐点的全区间最优解析实纯态曲线，又在 $p=99/100$ 有断连的正则实纤维。因此完整纤维的连通性不是这种最小纯态实现的必要条件。证毕。

<a id="entry-788"></a>

## 追加锚（本行以下为增补区）

<a id="section-220"></a>

## 220. 五维精确纯态纤维的球面—环面转变

**定义 220.1（固定三重谱处理器的实纤维）。** 取定义218.1的五维处理器、$a=1/10$ 及第218.5式的 $A,w$。记

$$
\mathcal F_p=\left\{v\in S^3:
 F(p,v):=p\,v^{\mathsf T}Av+\sqrt{p(1-p)}\,w^{\mathsf T}v-a=0\right\},
\qquad a<p<1.
\tag{220.1}
$$

令 $\chi,N$ 分别为第218.8、第218.9式的多项式，并置

$$
m(\mu)=\frac{N(\mu)}{\chi(\mu)},\qquad
R(\mu)=-m'(\mu),\qquad
C(\mu)=(\mu-a)(N\chi'-N'\chi)+N\chi-4a\chi^2.
\tag{220.2}
$$

$C$ 是一个八次有理多项式。令 $\mu_*$ 为其在
$(-51/1000,-50/1000)$ 中的唯一根，置

$$
p_*=\frac{R(\mu_*)}{R(\mu_*)+4}.
\tag{220.3}
$$

**定理 220.2（唯一内部临界层与两侧纤维类型）。** 定义220.1的全部实纤维具有如下性质：

$$
\frac{806}{1000}<p_*<\frac{807}{1000},\qquad
\mathcal F_p\cong
\begin{cases}
S^2,&a<p<p_*,\\[0pt]
S^1\times S^1,&p_*<p<1.
\end{cases}
\tag{220.4}
$$

同胚可取光滑微分同胚。除 $p=p_*$ 外，每个纤维都处处正则；在 $p_*$ 处恰有一个临界向量。总空间
$\mathcal Z=\{(p,v):a<p<1,\ v\in\mathcal F_p\}$ 仍为光滑三维流形，投影到 $p$ 在该点有唯一非退化、Morse 指数为一的临界点。

证明。 第218节已经证明 $A$ 的四个特征值 $\alpha_j$ 互异，且 $w$ 在每个特征方向上的坐标 $\beta_j$ 均非零。因此任何球面临界向量的乘子 $\mu$ 都不等于 $\alpha_j$。拉格朗日方程可写为

$$
v=c(\mu I-A)^{-1}w,\qquad
c=\frac12\sqrt{\frac{1-p}{p}}>0,\qquad
c^2R(\mu)=1.
\tag{220.5}
$$

预解式的谱展开给出
$R(\mu)=\sum_j\beta_j^2/(\mu-\alpha_j)^2>0$。由（220.5）

$$
p=\frac{R}{R+4},\qquad
v^{\mathsf T}Av=c^2(\mu R-m),\qquad
w^{\mathsf T}v=cm.
\tag{220.6}
$$

所以精确矩条件等价于

$$
\frac{\mu R+m}{R+4}=a,
\qquad
(\mu-a)R+m-4a=0.
\tag{220.7}
$$

清除非零分母 $\chi^2$ 后，末式正是 $C(\mu)=0$。反之，每个这样的实根均由（220.5）确定唯一单位临界向量及一个 $p\in(0,1)$；只须保留 $p>a$ 的根。

上述多项式的全部实根与所需符号可以在有理数域核对。第218节的系数还给出因式分解

$$
\chi(\mu)=
\frac{(2128000\mu^2-1532680\mu-533427)
      (2128000\mu^2+660680\mu-1391673)}
     {4528384000000},
\tag{220.8}
$$

$$
N(\mu)=
\frac{69(365560\mu-143041)(44840\mu^2-299\mu-41850)}
     {1132096000000}.
\tag{220.9}
$$

Sturm 计数给出 $C$ 恰有两个实根，均简单，且 $\gcd(C,\chi)=1$。它们的有理隔离区间分别为

$$
\left(-\frac{940771}{18504198},-\frac{678997}{13355317}\right),
\qquad
\left(\frac{34687170}{6868789},\frac{158239489}{31334746}\right).
\tag{220.10}
$$

在这些区间上对（220.2）的有理函数作区间运算，得到：

| 根 | $p=R/(R+4)$ | $R'(\mu)$ | $\mu-m(\mu)/4$ |
| --- | --- | --- | --- |
| $\mu_*$ | $(806/1000,807/1000)$ | $(-155,-154)$ | $(-780/1000,-779/1000)$ |
| 另一实根 | $(99/10000,101/10000)$ | $(-17/1000,-16/1000)$ | $(4999/1000,5001/1000)$ |

第二个根给出的 $p<a$，故在本定义的区间中，恰有一个临界参数及一个临界向量。区间运算中的分母均由（220.10）与 $\chi$ 的隔离区间严格分开，未使用近似根代替符号判定。

再核对临界点的非退化性。由第218节的特征值区间，
$\alpha_2<\mu_*<\alpha_3$，所以 $A-\mu_*I$ 有两个负、两个正方向。若 $v_*$ 为（220.5）的向量，则

$$
v_*^{\mathsf T}(A-\mu_*I)^{-1}v_*
=\frac{c^2}{2}R'(\mu_*)<0.
\tag{220.11}
$$

以 $v_*^\perp$ 为前三个坐标作 Schur 分解，惯性加法说明
二次型 $A-\mu_*I$ 在 $v_*^\perp$ 上的限制有一个负、两个正方向，且没有零方向。球面约束 Hessian 为该限制的正倍数 $2p_*$。

在临界向量处，对 $p$ 的偏导由（220.6）简化为

$$
\partial_pF=\mu-\frac m4
=\frac{\mu-a}{1-p}.
\tag{220.12}
$$

在唯一内部临界点该量严格为负。因此 $\mathcal Z$ 在此仍然光滑，可局部解出 $p$ 为 $v$ 的光滑函数；其临界 Hessian 是球面 Hessian 的正倍数 $-1/\partial_pF$，故指数为一。其他点由球面梯度非零而自动正则。

下面确定全部正则纤维的微分同胚类型。任取不包含 $p_*$ 的闭参数区间，球面紧性与无临界点给出球面梯度的正下界。向量场

$$
\frac{dv}{dp}
=-\frac{\partial_pF}{\|\nabla_{S^3}F\|^2}\,
  \nabla_{S^3}F
\tag{220.13}
$$

保持单位球面与精确矩方程，其流把该区间的任意两个纤维微分同胚对应。第218节已经证明 $p=1/5$ 的纤维是 $S^2$，所以整个 $(a,p_*)$ 区间的纤维均为 $S^2$。

上侧可由 $p=1$ 的极限纤维确定。使用坐标 $x=\sqrt{1-p}$，约束在 $x=0$ 附近解析，并且该端点的方程为
$v^{\mathsf T}Av=a$。由于
$\alpha_1<\alpha_2<a<\alpha_3<\alpha_4$，端点纤维处处正则。

在 $A$ 的正交特征坐标中，任取 $\xi,\eta\in S^1$，定义

$$
c_-(\xi)=\sum_{j=1}^{2}(a-\alpha_j)\xi_j^2>0,\qquad
c_+(\eta)=\sum_{j=1}^{2}(\alpha_{j+2}-a)\eta_j^2>0.
\tag{220.14}
$$

映射

$$
(\xi,\eta)\longmapsto
\left(
 \sqrt{\frac{c_+(\eta)}{c_-(\xi)+c_+(\eta)}}\,\xi,\quad
 \sqrt{\frac{c_-(\xi)}{c_-(\xi)+c_+(\eta)}}\,\eta
\right)
\tag{220.15}
$$

是从 $S^1\times S^1$ 到该端点纤维的微分同胚；其逆映射分别把前后两个非零二维分量归一化。端点正则性与紧性使（220.13）的同类参数流在 $x$ 坐标下适用，所以邻近 $p=1$ 的纤维也是环面。再沿 $(p_*,1)$ 的任意闭子区间运输，得到（220.4）的上侧结论。证毕。

**定理 220.3（纤维转变与最优纯态截面可以并存）。** 定理218.2的五维实解析纯态曲线可经过 $p=p_*$ 而始终留在 $\mathcal Z$ 的投影正则部分。另一方面，全部实精确纤维族不可能与一个固定流形在整个 $(a,1)$ 上作保持参数的微分同胚乘积分解。

证明。 第218节的光滑初始截面在最后一个过渡区间之后采用第三条规范分支；该分支的角度根导数在全区间严格为正。其沿截面的球面梯度因而在紧化区间具有正下界。解析逼近与标量修正可取得足够接近，保持该正则性，并仍精确匹配三个尖锐二阶数据，所以得到所述截面。

若存在整个纤维族的保持参数乘积分解，各参数纤维必彼此微分同胚。但（220.4）两侧的纤维分别为 $S^2$ 与 $S^1\times S^1$，它们的一阶 Betti 数分别为零与二，矛盾。证毕。

<a id="entry-790"></a>

## 追加锚（本行以下为增补区）

<a id="section-221"></a>

## 221. 单条纯态曲线的完整尖锐容量

**定义 221.1（复纯态截面的正则性）。** 对第213.4节的实共同处理器，在正 $q$ 规范中写

$$
\psi(p)=\sqrt p\,v(p)+\sqrt{1-p}\,q,\qquad
v\in q^\perp\otimes\mathbb C,\quad \|v\|=1.
\tag{221.1}
$$

$P$ 矩因此自动为 $p$。称一条精确截面正则，是指球面上实、虚两个 $T$ 矩方程的实微分线性无关。端点正则性在 $x=\sqrt{1-p}$ 紧化后的闭区间上理解。仍允许矩阵元素为复数；纯态性指实际密度矩阵始终为秩一。对所有 $0<a<1$、$d\ge3$，以 $\mathcal C^{\mathrm{pure}}_\nu(a;d)$ 表示实际联合支持维数不超过 $d$ 的一条完整精确纯态曲线可达到的最大尖锐点数，$\nu=1,\infty,\omega$ 分别指定 $C^1$、光滑、实解析；这把第219节的容量记号延伸到低参数区域。

**定理 221.2（每个低参数都有稳定三点纯态种子）。** 对每个固定 $0<a<1/2$，存在 $r\in(0,1)$ 及三个互异的 $h_1<h_2<h_3\in(a,1)$，满足
$\lambda_-(h_j)=-r$，使第213.4节的同一个五维处理器具有一条全区间、全输入精确的实解析复纯态准备曲线。其完整尖锐集合恰为 $\{2h_j-1:1\le j\le3\}$，各点的双侧普通曲率极限最优；其构造可从一个在闭紧化区间上正则的 $C^4$ 半代数截面出发，该截面在三个标记点附近分别等于规范分支。

证明。 置 $b=2a$、$\sigma=\sqrt{1-4a^2}$ 及 $c=a+2a^2$。第214.2节说明，对足够接近一且小于一的 $r$，有三个实际原像，且

$$
h_1(r),h_2(r)\longrightarrow c,\qquad
h_3(r)\longrightarrow1.
\tag{221.2}
$$

这也由 $P_{a,1}(h)=(h-1)(h-c)^2$、三段实际原像及根的连续性得到。三个不同根均简单，所有实际谱节点严格稳定。

按先三个正签名、后负签名的次序使用（219.2）。当 $r\uparrow1$，五维矩阵趋于

$$
V_*=
\begin{pmatrix}
0&\sigma&-b\sigma&0&0\\
0&b&\sigma^2&0&0\\
0&0&b&0&0\\
0&0&0&1&0\\
0&0&0&0&-1
\end{pmatrix},\qquad q=e_1.
\tag{221.3}
$$

记 $e=e_2$、$u_+=e_4$、$u_-=e_5$。四维空间
$\operatorname{span}\{q,e,u_+,u_-\}$ 被 $V_*$ 保持；其 $T_*=V_*^{\mathsf T}$ 压缩为
$\begin{psmallmatrix}0&0\\\sigma&b\end{psmallmatrix}\oplus(1)\oplus(-1)$。以下矩计算只用这个压缩，不假设该四维空间被 $T_*$ 保持。

先确定实际嵌入规范准备的极限。第213.25式的三个实等距嵌入属于紧 Stiefel 流形；沿 $r\uparrow1$ 的一个共同子列，它们同时收敛，且 $VU_i=U_iV_i$、$U_if=q$ 的关系传到极限。以下只沿这个子列取极限，这已足够选出一个实际稳定种子。对稳定特征值 $\lambda$，取 $q^{\mathsf T}x_\lambda=1$，并记单位特征向量
$n_\lambda=\sqrt{1-\lambda^2}\,x_\lambda$。由第213.21式，

$$
\langle q,n_\lambda\rangle=\sqrt{1-\lambda^2},\qquad
\langle n_\lambda,n_\mu\rangle=
\frac{\sqrt{(1-\lambda^2)(1-\mu^2)}}{1-\lambda\mu}.
\tag{221.4}
$$

早期两支的正签名趋于 $b<1$；其归一化正特征向量由（219.6）连续趋于
$x_b=q+(b/\sigma)e$。共同负单位特征方向在极限中只能为 $u_-$；极限等距嵌入把局部的三个不同特征方向分别送入 $q,x_b,u_-$。每条早期准备因此都有沿所选子列的极限，且都在这同一个三维空间内。负单位方向的符号可以不同。

更具体地，局部三维正特征向量可写为
$y_{\lambda_+}=(I-\lambda_+T_0)^{-1}f$。早期极限中 $\lambda_+\to b<1$，所以此向量及其与规范准备的内积连续。这样实际共同坐标中的 $e$ 分量收敛到一个实函数 $E(p)$。在 $p=c$，代入第211.17式得到

$$
E(c)=2a\sqrt{\frac{1+a}{1+2a}}>0,
\qquad c-E(c)^2=\frac a{1+2a}>0.
\tag{221.5}
$$

正号亦可直接从局部正特征向量取得：其第一个坐标的表达式中，$1-b(A_0)_{22}$、$(A_0)_{12}$ 及 $T_0f$ 的两个非零坐标均为正，分母为 $(1-b^2)(1+b)>0$。

矩约束与范数条件给出

$$
(1+b)E(p)^2+\sigma\sqrt{1-p}\,E(p)=a+p.
\tag{221.6}
$$

根不可能过零，故由（221.5）与连续性，$E(p)$ 始终是这个方程的正根。并且 $E(p)<\sqrt p$：把 $\sqrt p$ 代入左侧减右侧，所得
$a(2p-1)+\sigma\sqrt{p(1-p)}$ 严格为正。$p\ge1/2$ 时立即成立；$a<p<1/2$ 时由 $p(1-p)>a(1-a)>a^2$ 平方比较可得。因此两条早期准备分别趋于

$$
\sqrt{1-p}\,q+E(p)e+\epsilon_j\sqrt{p-E(p)^2}\,u_-,
\qquad \epsilon_j\in\{1,-1\},\quad j=1,2.
\tag{221.7}
$$

这些符号在所需的紧参数邻域中固定：其模有正下界，连续系数不能换号。并不需要两符号相反。

第三支的正、负签名分别趋于 $1,-1$。（221.4）说明 $q,n_{\lambda_+(h_3)},n_{-r}$ 趋于正交三向量 $q,u_+,u_-$，符号可吸收入相应系数。其范数、$P$ 矩与 $T$ 矩唯一确定两个单位方向的极限模，因此第三准备趋于

$$
\sqrt{1-p}\,q+\epsilon_+\sqrt{\frac{p+a}{2}}\,u_+
 +\epsilon_-\sqrt{\frac{p-a}{2}}\,u_-,
\qquad \epsilon_\pm\in\{1,-1\}.
\tag{221.8}
$$

早期局部模型在 $h=c$ 连续，规范角根的导数严格为正。第三局部模型在 $h=1$ 的 $P$ 压缩趋于
$\begin{psmallmatrix}a&\sqrt{1-a^2}\\\sqrt{1-a^2}&-a\end{psmallmatrix}$；在其从初始方向到正特征向量的规范角区间内，对固定 $p>a$，目标方程仍有唯一内部根且角导数为正。因此局部规范准备在所需小闭 $p$ 区间上一致收敛。结合等距嵌入的算子范数收敛，上述共同空间极限也在 $p=c$ 或任一固定 $p\in(c,1)$ 的小闭邻域内一致成立。单位系数的模严格为正，故相应符号在各邻域固定。

现在在极限处理器中构造两条正则连接。第一条位于 $p=c$：保持（221.7）的 $q,e$ 分量，只沿单位圆旋转 $u_-$ 的系数，把 $\epsilon_1$ 变成 $\epsilon_2$。$u_-$ 是约化的单位特征方向，故任意该相位都保持全部矩约束。

第二条取 $p_0=(c+1)/2$。对 $0\le E\le E(p_0)$，置

$$
\begin{aligned}
U_+(E)&=\frac{p_0+a-(1+b)E^2-\sigma\sqrt{1-p_0}\,E}{2},\\
U_-(E)&=\frac{p_0-a-(1-b)E^2+\sigma\sqrt{1-p_0}\,E}{2}.
\end{aligned}
\tag{221.9}
$$

$U_+$ 严格递减，在右端为零；$U_-$ 是凹函数，其两个端点值分别为 $(p_0-a)/2>0$ 与 $p_0-E(p_0)^2>0$。因此两个量在整段非负，后者严格为正。向量

$$
\sqrt{1-p_0}\,q+Ee+\sqrt{U_+(E)}\,u_+
 +\sqrt{U_-(E)}\,u_-
\tag{221.10}
$$

始终精确满足范数与全部矩约束，并把早期状态连接到第三支的极限模。两条约化单位方向的独立相位旋转可匹配任何所需端点符号。

两条连接都对复矩约束正则。沿它们，在 $e$ 坐标的虚方向上，虚 $T$ 矩的导数为 $-\sigma\sqrt{1-p}\ne0$，而实矩导数为零。实 $T$ 矩也有独立非零方向：若两个单位坐标均非零，保持其模平方之和而改变二者差即可；在 $U_+=0$ 的端点及第一条相位路径上，改变 $E$ 并补偿负单位坐标，导数为
$2(1+b)E+\sigma\sqrt{1-p}>0$。单位方向的相位不影响这些读数。所以两个球面微分沿整条紧路径独立。

这些连接可取 $C^4$ 半代数参数化。相位路径用有限个圆周 Nash 图；（221.10）在 $U_+=0$ 的端点可改用 $\sqrt{U_+}$ 作坐标，由上述非零导数解出 $E$。其余点取普通 Nash 图，端点四阶平坦的多项式重参数使有限段拼接为 $C^4$。

利用端点收敛，先对极限连接加入两端实际规范向量的小差值并归一化，再沿实、虚矩的两个球面梯度作二维隐式修正。梯度 Gram 矩阵沿紧路径一致正定，故对足够接近一的实际 $r<1$ 及附近的 $p$，这个修正统一存在，并保持两端的实际规范分支：两端本已满足方程，唯一小修正为零。全程保持正 $q$ 规范，可直接在（221.1）的 $v$ 球面上完成。

第一条连接可在 $p=c$ 附近使用，第二条在 $p_0$ 附近使用。选择互不相交且避开三个尖锐点的过渡区间，并用四阶平坦过渡参数，便得到一个全域 $C^4$ 半代数精确复截面，在每个 $h_j$ 附近恰等于相应规范分支。第一过渡区间虽可很窄，对每个固定 $r<1$ 仍有正宽度；这里不要求导数界对 $r\uparrow1$ 统一。

还须验证紧化端点的两矩正则性。沿任一实际实规范分支，实角导数在 $p=a,1$ 仍严格为正。$p<1$ 时，球面方向 $iv$ 给出的虚矩导数为
$-\sqrt{p(1-p)}\,w^{\mathsf T}v\ne0$，其中第211节的规范扇区保证 $w^{\mathsf T}v>0$。在 $p=1$，虚矩导数由二乘二压缩的反对称部分决定。对规范矩阵的两个非对角元，其平方之差满足

$$
(A_0)_{21}^2-(A_0)_{12}^2
=\frac{(1-h)\bigl[a^2-(h-2a^2)^2\bigr]}
       {h^2(1-a^2/h)}.
\tag{221.11}
$$

二元均为正，且 $a<h<1$；所以它们相等当且仅当 $h=a+2a^2$。实际 $r<1$ 的三个节点都不是这个临界位置。因此端点的虚矩球面导数仍非零，和实方向独立。所得截面在闭紧化区间上正则，并有 $C^4$ 半代数邻域延拓。

最后将实部、虚部视为 Euclidean 坐标，应用第218节引用的 Carbone–Fernando 定理1.1作任意精细的 $C^2$ Nash 逼近，再用有限 Hermite 多项式匹配三个节点的二阶数据并归一化。沿两个矩的球面梯度作二维解析修正；其 Jacobian 是一致正定的梯度 Gram 矩阵，统一解析隐函数定理给出同一小解。两个矩残差在标记点的二阶数据为零，所以修正的值、一阶和二阶导数也全为零。

因此最终解析曲线保持全部规范尖锐二阶数据。对复 $v$，实际纯态信息为

$$
I_Q-I_r=4p\left(\|v'\|^2-p|\langle v,v'\rangle|^2\right),
\tag{221.12}
$$

其中撇表示对 $u$ 求导。这个公式计入相位贡献；匹配实规范二阶数据便保留最优双侧普通曲率。精确矩给出全输入精确性，原空间谱计数及正签名的严格单调性给出五维实际支持和恰好三个尖锐位置。证毕。

**定理 221.3（纯态单曲线的完整容量分界）。** 对所有 $0<a<1$、整数 $d\ge3$，单条纯态准备曲线的三个正则性容量均为

$$
\mathcal C^{\mathrm{pure}}_1(a;d)
=\mathcal C^{\mathrm{pure}}_\infty(a;d)
=\mathcal C^{\mathrm{pure}}_\omega(a;d)
=\begin{cases}
\left\lfloor3(d-1)/4\right\rfloor,&0<a<1/2,\\[0pt]
\left\lfloor(d-1)/2\right\rfloor,&1/2\le a<1.
\end{cases}
\tag{221.13}
$$

更具体地，对每个 $m\ge1$ 可选取恰有 $m$ 个位置的集合 $S$，由一条完整解析纯态曲线达到，其最小实际维数为

$$
\begin{cases}
1+m+\lceil m/3\rceil,&0<a<1/2,\\[0pt]
1+2m,&1/2\le a<1.
\end{cases}
\tag{221.14}
$$

这些结论选择了位置集合；不声称每个预先指定的、任意分离的有限集合都已经在 $N(a,S)$ 维达到。

证明。 高参数区域已由定理219.3得到；以下固定 $0<a<1/2$。先取定理221.2给出的一个实际稳定三点种子，其共同负签名为 $-r_0$，三个正签名互异且严格稳定。

对 $m\ge3$，置 $k=\lceil m/3\rceil$，选取 $k$ 个互异且足够接近 $r_0$ 的参数。相应三次方程的简单根各自连续为三个实际位置簇。取前 $k-1$ 组全部三根，最后一组按需取一、二或三根，使总数恰为 $m$；三个种子簇都非空。所得正签名数为 $m$、负签名数为 $k$，共同处理器维数为 $N=1+m+k$。

在（219.2）的正交坐标中，让这些负签名参数趋于 $r_0$。共同处理器趋于一个具有重复稳定谱的 $N$ 维矩阵。式（219.6）的稳定预解式和 Gram 恒等式，把原五维种子等距嵌入该极限处理器：不同的五个归一化特征向量仍具有原正定 Gram 矩阵。嵌入 $W$ 满足

$$
Wq_0=q,\qquad VW=WV_0,\qquad
W^{\mathsf T}PW=P_0,\qquad W^{\mathsf T}TW=T_0.
\tag{221.15}
$$

这仍只要求 $V$ 的不变性及 $T$ 的压缩关系。

把种子的整个 $C^4$ 半代数截面嵌入后，两个矩的微分仍独立：原空间内的两个见证方向被等距保留。紧性给出统一正则性。因而对实际、互异且足够接近的负谱参数，二维隐式修正把这一背景截面继续到实际处理器，并保持闭区间上的正则性和邻域延拓。

每个簇内的规范分支，由稳定预解式与三向量 Gram 论证趋于原种子分支。于是，在三个种子位置的互不相交小邻域中，各实际分支与背景截面都落入同一正则复球面纤维图；该图有 $2N-5$ 个实自由坐标。沿参数次序在自由坐标的小凸球中连接，并在每个实际节点附近采用对应规范分支，就得到同时保留全部 $m$ 组规范二阶数据的正则 $C^4$ 半代数截面。再用定理221.2的二维解析修正论证，得到一条完整解析纯态曲线。两个矩、实际信息公式和正谱排除论证分别给出全输入精确性、最优普通曲率和完整尖锐集合。

$m=1$ 用第211节的三维规范构造。对 $m=2$，令 $R(h)=-\lambda_-(h)$。按第214.11式把它在右端连续补为一后，它在 $[c,1]$ 两端取一，在内部严格小于一，因此在某个 $h_*>c$ 取得内部最小值。解析性和非恒定性使该最小点局部严格。足够接近最小值而略大的同一 $R$ 值，在 $h_*$ 的任意小邻域中有左右两个原像。该中心非临界，故定理219.2给出一条四维实解析实纯态曲线。这完成低参数区域（221.14）的达到性。

最后，第214.3节的原空间谱下界对一条纯态曲线仍适用。低参数每个负签名至多支撑三个位置，高参数至多一个，分别给出（221.14）的维数下界及（221.13）的容量上界。取
$m=\lfloor3(d-1)/4\rfloor$ 或 $m=\lfloor(d-1)/2\rfloor$，对应整数维数不超过 $d$，上述解析构造达到该上界。证毕。

<a id="entry-792"></a>

## 追加锚（本行以下为增补区）

<a id="section-222"></a>

## 222. 复相位转接的五维分离双点实现

**定义 222.1（两条规范准备的交叉反对称矩）。** 固定 $0<a<h_A<h_B<1$，取第213.4节的共同处理器，以及由第211节嵌入的两条实规范准备 $x(r),y(t)$。参数 $r,t$ 表示各自的 $P$ 期望，均在 $(a,1)$ 内。定义

$$
\omega(r,t)=x(r)^{\mathsf T}(T-T^{\mathsf T})y(t).
\tag{222.1}
$$

本节在正 $q$ 规范中使用纯向量，但允许其余坐标为复数。

**定理 222.2（分离双点的最小纯态维数达到）。** 对

$$
a=\frac7{10},\qquad h_A=\frac{39}{50},\qquad h_B=\frac{23}{25},\qquad
S=\left\{\frac{14}{25},\frac{21}{25}\right\},
\tag{222.2}
$$

第213.4节的同一个五维处理器存在一条全区间、全输入精确的实解析复纯态准备曲线。其完整尖锐集合恰为 $S$，两点的双侧普通曲率极限均最优，且

$$
d_1(a,S)=d_\infty(a,S)=d_\omega(a,S)=5.
\tag{222.3}
$$

此外，（222.2）的三参数 $(a,h_A,h_B)$ 有一个开邻域，其中每组参数都满足对应的五维达到性结论。

证明。 先给出连接所需的精确构造。对实数 $c,d\ge0$、$c^2+d^2=1$，置

$$
\Psi(c,d;r,t)=c\,x(r)+i d\,y(t).
\tag{222.4}
$$

两条规范准备是实向量、单位向量，且各自的 $T$ 期望都为 $a$。因此直接展开得到

$$
\|\Psi\|=1,\qquad
\langle P\rangle_\Psi=c^2r+d^2t,\qquad
\operatorname{Re}\langle T\rangle_\Psi=a,\qquad
\operatorname{Im}\langle T\rangle_\Psi=cd\,\omega(r,t).
\tag{222.5}
$$

若在某个 $p_0\in(h_A,h_B)$ 有

$$
\omega(p_0,p_0)=0,\qquad
\partial_1\omega(p_0,p_0)>0>\partial_2\omega(p_0,p_0),
\tag{222.6}
$$

则（222.4）在 $r=t=p_0$ 给出从 $x(p_0)$ 到 $i y(p_0)$ 的精确纯态路径。该路径还可延伸到附近的 $p$。实际求解

$$
c^2r+d^2t=p,\qquad \omega(r,t)=0.
\tag{222.7}
$$

对 $(r,t)$ 的 Jacobian 行列式为

$$
c^2\partial_2\omega-d^2\partial_1\omega<0.
\tag{222.8}
$$

该不等式在整段闭四分之一圆上成立，包括两端。紧性与解析隐函数定理给出统一的小 $p$ 邻域，以及唯一靠近 $(p_0,p_0)$ 的解析解。参数可取
$c=(1-s^2)/(1+s^2)$、$d=2s/(1+s^2)$、$0\le s\le1$，因此路径及延伸均可选 Nash。$s=0$ 时实际向量为 $x(p)$；$s=1$ 时为 $i y(p)$。

在路径内部，$(r,t)$ 的变化独立控制 $P$ 矩与虚 $T$ 矩。另改变一条规范分支的角坐标，可独立改变实 $T$ 矩，因为其角导数严格为正，而前两种变化恒保持实 $T$ 矩。因此单位复球面上的三个实矩约束具有满秩三。

在实端点，实方向上的 $P$ 矩与实 $T$ 矩独立；虚方向给出另外一个非零导数。更直接地，写
$\psi=\sqrt p\,v+\sqrt{1-p}\,q$，$v$ 为实单位向量，$w=Tq$。沿固定 $q$ 规范的球面方向 $iv$，虚 $T$ 矩的导数是
$-\sqrt{p(1-p)}\,w^{\mathsf T}v$。第211节规范扇区内 $w^{\mathsf T}v>0$，所以该导数非零。两端也具有满秩三。沿（222.7）的紧连接路径，缩小参数邻域后仍保持此正则性。

现在核对（222.2）的连接条件。令三维规范矩阵按第211.17式写为

$$
T_i=\begin{pmatrix}A_i&b_i\\0&0\end{pmatrix},\qquad i=A,B.
\tag{222.9}
$$

两个等距嵌入的交叉 Gram 矩阵为 $Q=\operatorname{diag}(C,1)$，其中

$$
C-A_ACA_B^{\mathsf T}=b_Ab_B^{\mathsf T}.
\tag{222.10}
$$

因为两个 $A_i$ 的谱均严格稳定，该 Stein 方程唯一可解。由第213.25式的交织关系，

$$
\omega(r,t)=\psi_A(r)^{\mathsf T}
       (T_AQ-QT_B^{\mathsf T})\psi_B(t),
\tag{222.11}
$$

右侧只涉及两个三维规范模型。

取 $p_L=88831042/10^8$、$p_U=88831044/10^8$，并令 $I=[p_L,p_U]$。在规范坐标 $y=\tan\Theta$ 中，单位向量写为

$$
\psi_i(p,y)=\left(
\frac{\sqrt p}{\sqrt{1+y^2}},\quad
\frac{\sqrt p\,y}{\sqrt{1+y^2}},\ \sqrt{1-p}\right)^{\mathsf T}.
\tag{222.12}
$$

规范根由 $\psi_i^{\mathsf T}T_i\psi_i=a$ 及第211节的唯一扇区指定。以下有理区间的两端分别给出严格负、严格正残差：

| 分支与参数 | $y$ 的严格包围区间 |
| --- | --- |
| $A,p_L$ | $(0.01907958338866,0.01907958338867)$ |
| $A,p_U$ | $(0.01907959115611,0.01907959115612)$ |
| $B,p_L$ | $(0.00183812215476,0.00183812215477)$ |
| $B,p_U$ | $(0.00183811994859,0.00183811994860)$ |

在整个 $p\in I$ 上，较宽的区间
$y_A\in(0.019078,0.019081)$、$y_B\in(0.001837,0.001840)$ 也分别具有一致的严格异号端点残差，且都位于规范扇区内。因而这些是整段规范分支的包围，不只约束两个端点。对角度方程隐式求导，再代入（222.10）—（222.11），得到以下严格区间：

| 量 | 严格范围 |
| --- | --- |
| $\omega(p_L,p_L)$ | $(4.3499,4.3500)\cdot10^{-9}$ |
| $\omega(p_U,p_U)$ | $(-5.3979,-5.3977)\cdot10^{-9}$ |
| $\partial_1\omega$，在 $I^2$ 上 | $(0.66804,0.66805)$ |
| $\partial_2\omega$，在 $I^2$ 上 | $(-1.15544,-1.15542)$ |

这些界由有理区间、正平方根的区间运算与四维线性方程（222.10）得到；角导数在所用区间严格为正，故隐式求导的分母不含零。端点异号给出一个 $p_0\in I$；两个偏导的和严格为负还保证该根在 $I$ 内唯一。于是（222.6）成立。

由于（222.4）的 $q$ 坐标为
$c\sqrt{1-r}+id\sqrt{1-t}$，其模由（222.7）恰为 $\sqrt{1-p}>0$。除以这个坐标的单位相位，就得到正 $q$ 规范中的 Nash 连接；两端分别是 $x(p)$ 与 $y(p)$。在一个避开 $h_A,h_B$ 的小 $p$ 过渡区间中，用端点四阶平坦的多项式 $s(p)$ 走过该连接，其他地方采用相应规范分支。这得到一条 $C^4$ 半代数复纯态截面，在两个尖锐位置附近恰等于各自的规范分支。

为解析化，继续使用正 $q$ 规范，写
$\psi=\sqrt p\,v+\sqrt{1-p}\,q$、$v\in\mathbb C^4$、$\|v\|=1$。这样 $P$ 矩自动精确；球面上还需满足实、虚两个 $T$ 矩方程。上述满秩三恰保证这两个方程在所选截面上的球面梯度独立。

在紧化坐标 $x=\sqrt{1-p}$ 的两个端点，独立性仍成立。$p=a$ 时，规范分支的实角导数严格为正，前述 $iv$ 方向的虚矩导数非零。$p=1$ 时，实角导数仍为正，而两个三维模型的压缩反对称部分满足

$$
(A_A)_{21}-(A_A)_{12}\in(0.3540,0.3541),\qquad
(A_B)_{21}-(A_B)_{12}\in(0.0718,0.0719).
\tag{222.13}
$$

非零二乘二反对称矩阵作用于非零实单位向量不为零，因而端点的虚矩球面导数也不消失。实、虚方向相互独立。截面在闭紧化区间上于是具有统一的正则性下界，并可在两端向外延拓。

对实部与虚部坐标一并应用第218节所用的 Euclidean $C^2$ Nash 逼近，再作有限 Hermite 修正以匹配两个标记点的二阶数据，最后归一化。记实、虚矩的球面切向梯度为 $g_1,g_2$。它们的实 Gram 矩阵在紧区间上一致正定；沿 $\tau_1g_1+\tau_2g_2$ 移动并重新归一化，两个矩残差对 $(\tau_1,\tau_2)$ 的 Jacobian 就是该 Gram 矩阵。统一解析隐函数定理因此给出一个小的二维解析修正，恢复两个精确矩方程。

在标记点，归一化保留二阶数据，两个矩残差的二阶数据均为零。逐次微分隐式方程，并用 Jacobian 的可逆性，得 $\tau=\tau'=\tau''=0$。于是解析修正精确保留两组规范尖锐二阶数据。

对一般复向量，实际纯态信息恒等式是

$$
I_Q-I_r=4p\left(
 \|v'\|^2-p|\langle v,v'\rangle|^2\right),
\tag{222.14}
$$

其中撇表示对 $u$ 求导。它由
$\langle\psi,\psi'\rangle=p\langle v,v'\rangle$ 与纯态信息公式直接得到。因此不能略去复相位项。构造精确匹配实规范分支的二阶数据，故（222.14）给出两点的最优普通曲率极限。两个完整矩约束给出全输入精确性；正谱只有两个指定正签名，排除额外尖锐位置。高参数负签名互异，原空间谱必要性给出五维下界，证明（222.3）。

最后，上述端点异号、偏导符号、稳定谱、规范扇区和紧截面的梯度独立性均为严格条件。它们在三参数的小开邻域中保持；同样的连接、紧化和二阶数据修正逐参数适用，得到所述开放参数族。证毕。

<a id="entry-794"></a>

## 追加锚（本行以下为增补区）

<a id="section-223"></a>

## 223. 一个负单位方向连接任意指定尖锐集合

**定义 223.1（稳定部分与正半球）。** 固定 $0<a<1$ 及非空有限集合 $S\subset J_a$，记 $m=\#S$、$N=N(a,S)$。定理213.4的共同处理器称为稳定，若其谱不含 $-1$；按第214节，这等价于 $S$ 不包含低参数临界位置 $u_c=2(a+2a^2)-1$。对稳定部分，在 $q^\perp\oplus\mathbb Rq$ 中写

$$
T=\begin{pmatrix}B&b\\0&0\end{pmatrix},\qquad
BB^{\mathsf T}+bb^{\mathsf T}=I,
\qquad H=\frac{B+B^{\mathsf T}}2.
\tag{223.1}
$$

这里 $V=T^{\mathsf T}$，$Vq=0$，$V^{\mathsf T}V=I-qq^{\mathsf T}$。下述稳定 Gram 类允许第213节 Cauchy Gram 构造中的任意互异实谱节点，要求包含零及至少一个非零节点，且全部位于 $(-1,1)$；剩余谱不必成对对应一个完整指定集合。特别地，分离临界 $-1$ 方向后仍保留正特征值 $2a$，该稳定部分通常不同于删去临界位置后的共同处理器。正半球由 $H$ 的最大特征向量决定。路径的正则性指其每个像点都是约束的正则点；四阶平坦参数可以在拼接处具有零速度。

**引理 223.2（对称压缩的循环性与规范分支的共同正方向）。** 定义223.1的任意稳定 Gram 算子的 $H$ 具有简单谱，$b$ 在每个特征方向上的投影非零。令 $\alpha$ 是最大特征值，取对应单位向量 $u$，定向为 $u^{\mathsf T}b>0$。则其中每条嵌入的非临界规范准备
$\psi_i(p)=\sqrt{1-p}\,q+\sqrt p\,v_i(p)$ 都满足

$$
u^{\mathsf T}v_i(p)>0\qquad(a\le p\le1).
\tag{223.2}
$$

证明。 对每个非零稳定特征值 $\lambda$，取第213节的特征向量 $x_\lambda$，使 $q^{\mathsf T}x_\lambda=1$，置 $e_\lambda=(x_\lambda-q)/\lambda$。由分块的 $Vx_\lambda=\lambda x_\lambda$ 得

$$
B^{\mathsf T}e_\lambda=\lambda e_\lambda,
\qquad b^{\mathsf T}e_\lambda=1,
\qquad
(I-2\lambda H+\lambda^2I)e_\lambda=b.
\tag{223.3}
$$

最后一式由 $BB^{\mathsf T}+bb^{\mathsf T}=I$ 得到。这些 $e_\lambda$ 构成 $q^\perp$ 的一组基。若 $Hy=\mu y$ 且 $y^{\mathsf T}b=0$，则（223.3）给出
$(1-2\lambda\mu+\lambda^2)y^{\mathsf T}e_\lambda=0$。因为 $|\mu|\le1$、$|\lambda|<1$，该系数严格为正，所以 $y=0$。每个特征空间因而是一维，且 $b$ 的投影非零。实际上全部特征值严格位于 $(-1,1)$：若实 Rayleigh 商达到 $\pm1$，收缩算子的 Cauchy–Schwarz 等号会给出 $T$ 的 $\pm1$ 特征向量，违反稳定性。

现取任一规范三维块，记其二维压缩为 $B_i$、末列为 $b_i$，以及 $\beta_i=-\det B_i\in(0,1)$。第211.24—211.26式给出两个非对角元均正，并且

$$
(I-B_i)^{-1}b_i>0
\quad\text{逐坐标成立}.
\tag{223.4}
$$

由奇异值 $1,\beta_i$，其对称压缩的最大特征值为
$\rho_i=(\operatorname{tr}B_i+1+\beta_i)/2$。定义 $D_i(s)=I-2sB_i+B_i^2$。Cayley–Hamilton 恒等式给出

$$
D_i(\rho_i)=(1+\beta_i)(I-B_i),\qquad
D_i(1)=(I-B_i)^2.
\tag{223.5}
$$

对 $\rho_i\le s\le1$，令 $\eta=(s-\rho_i)/(1-\rho_i)$，于是

$$
D_i(s)=\bigl[(1-\eta)(1+\beta_i)I+\eta(I-B_i)\bigr](I-B_i).
\tag{223.6}
$$

把第一个因子写为 $L_i=c_0I-\eta B_i$，其中 $c_0=1+\beta_i-\eta\beta_i\ge1$。其对角元严格为正、非对角元非正，且 $\det L_i=(c_0-\eta\lambda_+)(c_0-\eta\lambda_-)>0$，所以二乘二逆矩阵公式给出逐项非负且对角元为正的逆。$I-B_i$ 同样如此。两个因子都是 $B_i$ 的多项式而相互交换，故 $D_i(s)^{-1}b_i=L_i^{-1}(I-B_i)^{-1}b_i>0$；这里使用（223.4），并不要求 $b_i$ 自身逐坐标为正。

令 $U_i:\mathbb R^2\to q^\perp$ 为规范嵌入的二维部分。由压缩关系有 $\alpha\ge\rho_i$。把（223.3）分别与 $u$ 配对，并使用局部的两个稳定特征向量作为基，得到

$$
U_i^{\mathsf T}u=(u^{\mathsf T}b)D_i(\alpha)^{-1}b_i>0.
\tag{223.7}
$$

具体地，两边与局部 $e_\lambda$ 的内积都为
$(u^{\mathsf T}b)/(1-2\alpha\lambda+\lambda^2)$，故两向量相同。规范方向的坐标为 $(\cos\Theta_i,\sin\Theta_i)$，其中 $0\le\Theta_i<\bar\theta_i<\pi/2$。因此（223.7）给出（223.2）。证毕。

**引理 223.3（正半球内的超水平连接）。** 设 $H$ 为实对称矩阵，其最大特征值 $\alpha$ 简单，单位特征向量为 $u$；设 $u^{\mathsf T}\beta>0$。对单位球面上的函数

$$
f(v)=v^{\mathsf T}Hv+2\beta^{\mathsf T}v,
\tag{223.8}
$$

任意两个满足 $u^{\mathsf T}v>0$、$f(v)\ge c$ 的点，均可在同一正半球的该超水平集中连接。若 $c$ 严格低于最大值，连接可在离开正则边界端点后完全处于 $f>c$，并可取有限分段 Nash、拼接后 $C^4$ 的半代数路径。

证明。 沿球面梯度上升，记 $z=u^{\mathsf T}v$、$\beta_+=u^{\mathsf T}\beta>0$，则

$$
\dot z=2\bigl(\alpha-v^{\mathsf T}Hv-\beta^{\mathsf T}v\bigr)z+2\beta_+.
\tag{223.9}
$$

取括号绝对值的正上界 $M$，比较方程给出

$$
z(t)\ge e^{-2Mt}z(0)+\frac{\beta_+}{M}(1-e^{-2Mt})>0.
$$

因此轨线始终留在正半球，且 $z$ 有严格正的统一下界。函数 $f$ 沿轨线增加，其导数为球面梯度的模平方；紧性和该导数的一致连续性使任意极限点都为临界点。

正半球内的临界点满足 $(\mu I-H)v=\beta$，而 $z=\beta_+/(\mu-\alpha)>0$ 强制 $\mu>\alpha$。方程 $\|(\mu I-H)^{-1}\beta\|=1$ 在 $(\alpha,\infty)$ 严格递减，从无穷降到零，故恰有一解。该临界点是唯一全局极大点，因为对单位 $v$，与该点 $v_*$ 的函数差为
$f(v_*)-f(v)=(v-v_*)^{\mathsf T}(\mu I-H)(v-v_*)$。所以所有正半球上升轨线都趋向同一个 $v_*$。

由两条上升轨线及极大点附近的小邻域即可连接任意两点。若端点位于正则水平 $f=c$，先沿一个局部 Nash 法向弧进入 $f>c$。严格超水平部分是开半代数流形；上述连续连接保证所需分支路径连通，可在有限个 Nash 图中用多项式弧连接，并作端点四阶平坦重参数。若 $c$ 等于最大值，集合只含 $v_*$。证毕。

**定理 223.4（任意指定集合的一个负单位方向上界）。** 对任意 $0<a<1$ 及非空有限 $S\subset J_a$，有

$$
N(a,S)\le d_1(a,S)\le d_\infty(a,S)\le d_\omega(a,S)
        \le\min\{3m,N(a,S)+1\}.
\tag{223.10}
$$

可以选择一条全区间实解析的实向量纯态准备，完整尖锐集合恰为 $S$，并在所有指定点达到最优双侧普通曲率极限。若 $0<a<1/2$ 且 $u_c=2(a+2a^2)-1\in S$，则更有

$$
d_1(a,S)=d_\infty(a,S)=d_\omega(a,S)=N(a,S).
\tag{223.11}
$$

证明。 先设原共同处理器稳定。只添加一个约化的负单位方向，令
$\widetilde T=T\oplus(-1)$、$\widetilde P=P\oplus1$。固定 $p\in(a,1)$，在正 $q$ 规范中写

$$
\psi=\sqrt{1-p}\,q+w+z e_-,\qquad
z\ge0,
\qquad \|w\|^2+z^2=p.
\tag{223.12}
$$

范数和精确矩方程等价于

$$
g_p(w):=w^{\mathsf T}(I+H)w+\sqrt{1-p}\,b^{\mathsf T}w=p+a,
\qquad \|w\|\le\sqrt p.
\tag{223.13}
$$

稳定性保证 $I+H$ 正定。对每个单位方向 $n$，方程 $g_p(rn)=p+a$ 恰有一个正根 $r=r_p(n)$，且径向导数严格为正。该根不超过 $\sqrt p$ 当且仅当

$$
\phi_p(n):=p\,n^{\mathsf T}Hn+\sqrt{p(1-p)}\,b^{\mathsf T}n\ge a.
\tag{223.14}
$$

于是半纤维 $z\ge0$ 是这一超水平集的径向提升：
$w=r_p(n)n$、$z=\sqrt{p-r_p(n)^2}$。规范状态对应其边界上的 $n=v_i(p)$。引理223.2把它们放在同一正半球；引理223.3应用于 $\phi_p/p$，便把任意两条规范准备的值连接起来，而且路径内部可取 $z>0$。

内部的实矩约束处处正则。若 $z>0$ 的点在固定范数球面上临界，拉格朗日乘子由负单位坐标强制为 $-1$，从而 $\nabla g_p(w)=0$。但正定二次函数 $g_p$ 的唯一驻点是最小值点，其值不超过 $g_p(0)=0$，不可能等于 $p+a>0$。边界的规范端点由第211节的严格正角导数保持正则。为显式处理边界平方根，选取经过规范方向的 Nash 球面弧 $n(t)$，使 $d\phi_p(n(t))/dt$ 在 $t=0$ 非零。考虑

$$
\mathcal F(z,t)=(p-z^2)n(t)^{\mathsf T}Hn(t)
 +\sqrt{1-p}\sqrt{p-z^2}\,b^{\mathsf T}n(t)-z^2-a.
$$

在 $(z,t)=(0,0)$，有 $\mathcal F=0$、$\partial_t\mathcal F\ne0$，Nash 隐函数给出 $t=\chi(z^2)$。因此
$z\mapsto(\sqrt{p-z^2}\,n(\chi(z^2)),z)$ 是进入 $z>0$ 的 Nash 边界路径。把这些路径的内部端点在严格超水平集中连接，再作有限四阶平坦拼接，便得到处处位于标量约束正则点集合中的 $C^4$ 半代数路径。

在相邻指定位置 $h_i,h_{i+1}$ 之间各选一个 $p_i$ 并使用上述连接。按第218.12式的方法，先补偿实际端点的参数变化并归一化，再沿非零球面梯度作标量隐式修正，把紧路径延伸到 $p_i$ 的小邻域；两端原已精确，故修正在两端为零。四阶平坦拼接得到一个全域 $C^4$ 半代数实截面，在每个 $h_i$ 附近等于相应规范分支。两端沿规范尾部，在 $x=\sqrt{1-p}$ 紧化坐标中具有正则解析延拓。

对该紧截面作实 Euclidean $C^2$ 逼近、有限 Hermite 二阶数据修正、归一化及第218.14式的解析标量修正，便得到一条全域实解析实纯态曲线。亦可逐坐标逼近二阶导数再积分两次，使用多项式完成同一 Euclidean 逼近。具体地，设归一化逼近为 $y(x)$，令 $g=(I-yy^{\mathsf T})\nabla_yF(x,y)$，统一正则性使 $\|g\|$ 有正下界。沿 $(y+\tau g)/\sqrt{1+\tau^2\|g\|^2}$ 修正时，矩残差对 $\tau$ 在零点的导数为 $\|g\|^2$。紧性给出一个统一小区间，其中该导数仍严格为正；再把逼近取得充分精细，使残差在区间两端异号，便得到每个 $x$ 上唯一的小根。解析隐函数与唯一性将其接为同一个解析函数。标记点残差的二阶数据为零，逐次微分得修正的值、一阶和二阶导数均为零。全部规范尖锐二阶数据因此保留。实纯态信息恒等式 $I_Q-I_r=4p\|dv/du\|^2$ 给出最优普通曲率，两个矩给出全输入精确性。

只添加 $-1$ 没有增加任何内部正签名。由正签名严格单调及第213节的谱必要性，完整尖锐集合恰为 $S$；不声称普通校准集合也只有这些点。实际联合支持不超过 $N+1$，结合已有 $3m$ 上界与谱下界，得到稳定情形的（223.10）。

再设 $S$ 包含临界位置。若 $m=1$，第211节已经在三维达到 $N$。以下设 $m\ge2$。将已有的约化 $-1$ 方向从共同处理器分离，剩余 $T_s$ 稳定，仍有同一个 $q$ 和秩一缺陷。所有非临界规范准备都位于这个稳定部分。临界规范准备在正交坐标中为

$$
\psi_c(p)=\sqrt{1-p}\,q+E(p)e+z(p)e_-,\qquad
(1+2a)E(p)^2+\sqrt{1-4a^2}\sqrt{1-p}\,E(p)=p+a.
\tag{223.15}
$$

第221.5式的规范代入给出 $E(a+2a^2)>0$，故连续性选择方程的正根。代入 $\sqrt p$ 后的严格比较
$a(2p-1)+\sqrt{1-4a^2}\sqrt{p(1-p)}>0$ 在整个 $[a,1]$ 成立；在 $p<1/2$ 时其平方比较为 $p(1-p)>a^2$。所以 $0<E(p)<\sqrt p$，$z(p)^2=p-E(p)^2>0$。定向已有负单位方向，使整条临界分支 $z(p)>0$。

令 $b_c=2a$、$\sigma=\sqrt{1-b_c^2}$。临界稳定方向满足
$e=\sigma(x_{b_c}-q)/b_c$。对稳定部分 $H_s$ 的最大特征向量 $u_s$，由（223.3）有

$$
u_s^{\mathsf T}e=
\frac{\sigma\,u_s^{\mathsf T}b_s}
     {1-2b_c\alpha_s+b_c^2}>0.
\tag{223.16}
$$

临界准备的径向方向因此也在与全部非临界规范准备相同的正半球中。它在（223.13）的提升中是 $z>0$ 的内部点；非临界准备是 $z=0$ 的边界点。引理223.3在稳定部分给出全部所需超水平连接。沿相同的正则路径、紧化和二阶数据修正完成全域纯态曲线，全程只使用原来的 $N$ 维空间。谱下界迫使实际联合支持恰为 $N$，得到（223.11），也完成一般情形的（223.10）。证毕。

**注记 223.5（剩余的一维差距）。** 任意预先指定有限位置集合的纯态最小维数，现在被夹在谱下界与谱下界加一之间；含临界位置的集合已经在下界达到。一般稳定集合能否也全部在 $N(a,S)$ 维达到，仍未由本节解决。连接的几何依据是规范分支的共同正方向及其超水平提升，不是全部精确纤维的连通性；纯态与混态最小维数也未被一般性地等同。

<a id="entry-796"></a>

## 追加锚（本行以下为增补区）

<a id="section-224"></a>

## 224. 单独增加正单位方向仍不能连接的精确实例

**定义 224.1（共享负签名的四维双点程序）。** 取

$$
a=\frac9{20},\qquad r=\frac{999999}{1000000},\qquad
c=a+2a^2=\frac{171}{200},
\tag{224.1}
$$

并令

$$
P(h)=\frac{(h^2-a^2)(h+ar)^2-(h-a^2)r^2[h(r+2a)-a]^2}{h}.
\tag{224.2}
$$

这是第214节的首一三次多项式。以下表格的端点值区间都是严格有理不等式：

| 根的区间 $(L,R)$ | $10^6P(L)$ 的区间 | $10^6P(R)$ 的区间 |
| --- | --- | --- |
| $(17/20,851/1000)$ | $(-9/10,-4/5)$ | $(2/5,1/2)$ |
| $(859/1000,43/50)$ | $(3/5,7/10)$ | $(-3/5,-1/2)$ |
| $(9997/10000,9999/10000)$ | $(-17/10,-8/5)$ | $(5/2,13/5)$ |

三个互不相交区间的端点异号给出三个根 $h_1<h_2<h_3$，次数三保证各自唯一。这些区间都满足 $h(r+2a)-a>0$，故未平方的物理条件给出 $\lambda_-(h_j)=-r$。取

$$
S=\{2h_1-1,2h_3-1\},\qquad N(a,S)=4.
\tag{224.3}
$$

两个指定位置都非临界。置

$$
L(h)=\frac{h(r+2a)-a}{h+ar},\qquad
\lambda=L(h_1),\quad\mu=L(h_3).
\tag{224.4}
$$

第214.5式表明它们是相应正签名。对端点代入严格递增的 $L$ 得

$$
\frac{896}{1000}<\lambda<\frac{897}{1000},\qquad
\frac{4999}{5000}<\mu<1.
\tag{224.5}
$$

**定理 224.2（正单位扩张的实纯态阻碍）。** 对定义224.1的共同四维处理器，只增加一个约化的 $+1$ 单位方向，得到的同一个五维处理器不存在一条全区间实 $C^1$ 精确纯态准备曲线，使（224.3）的两个位置都尖锐。这个结论允许曲线经过奇异状态，也不要求其余位置正则。

本定理只排除这个固定的正单位扩张及实准备；不对任意其他处理器或复准备给出五维不可能性。

证明。 写 $s_\lambda=\sqrt{1-\lambda^2}$、$s_\mu=\sqrt{1-\mu^2}$、$\delta=\sqrt{1-r^2}$。按第219.2式的次序，可取共同处理器

$$
V=\begin{pmatrix}
0&s_\lambda&-\lambda s_\mu&\lambda\mu\delta\\
0&\lambda&s_\lambda s_\mu&-\mu s_\lambda\delta\\
0&0&\mu&s_\mu\delta\\
0&0&0&-r
\end{pmatrix},\qquad q=e_1,
\qquad T=V^{\mathsf T}.
\tag{224.6}
$$

后三列正交归一，故 $V^{\mathsf T}V=I-qq^{\mathsf T}$。它与第213节的 Gram 处理器正交等价。令 $T_+=T\oplus1$、$P_+=I-qq^{\mathsf T}$。对其第211.18式固定通道，任意实精确准备在正 $q$ 规范中都满足

$$
\|\psi\|=1,\qquad q^{\mathsf T}\psi=\sqrt{1-p},\qquad
\psi^{\mathsf T}T_+\psi=a.
\tag{224.7}
$$

先建立不能穿越的超平面。置 $b_*=9/10$、$\sigma=\sqrt{19}/10$，并定义比较算子

$$
V_*=
\begin{pmatrix}
0&\sigma&0&0\\
0&b_*&0&0\\
0&0&1&0\\
0&0&0&-1
\end{pmatrix},\qquad T_{*,+}=V_*^{\mathsf T}\oplus1.
\tag{224.8}
$$

由（224.5）有 $|s_\lambda-\sigma|<9/1000$。按列计算，

$$
\begin{aligned}
\|V-V_*\|_F^2
={}&(s_\lambda-\sigma)^2+(\lambda-b_*)^2
+s_\mu^2+(1-\mu)^2+\delta^2+(1-r)^2\\
<&\left(\frac9{1000}\right)^2+\left(\frac1{250}\right)^2
 +\frac1{2500}+\left(\frac1{5000}\right)^2
 +\frac1{500000}+10^{-12}<\frac1{1600}.
\end{aligned}
\tag{224.9}
$$

所以 $\|T_+-T_{*,+}\|<1/40$。写 $\psi=(x,y,z,\eta,\zeta)$，其中 $x=\sqrt{1-p}$。若 $\eta=0$，单位范数给出 $y^2+z^2+\zeta^2=p$，于是

$$
\psi^{\mathsf T}T_{*,+}\psi
=p-(1-b_*)y^2+\sigma\sqrt{1-p}\,y
\ge b_*p-\sigma\sqrt{p(1-p)}.
\tag{224.10}
$$

此处用的是 $y\in[-\sqrt p,\sqrt p]$ 上凹二次函数的端点最小值。对 $p\ge4/5$，有 $\sigma<1/2$、$\sqrt{p(1-p)}\le2/5$，从而

$$
\eta=0,\ p\ge\frac45
\quad\Longrightarrow\quad
\psi^{\mathsf T}T_+\psi>
\frac{13}{25}-\frac1{40}=\frac{99}{200}>a.
\tag{224.11}
$$

这说明该参数区间内没有实精确状态可以穿过 $\eta=0$，并未限制新增坐标 $\zeta$ 的符号。

其次说明尖锐节点的状态没有任意选择的自由。把第213.2节的等号推导直接用于固定的 $P_+,T_+$，每个尖锐节点 $h_i$ 都强制一个 $(V\oplus1)$ 不变的规范三维块，其谱为 $\{0,\lambda_+(h_i),-r\}$。五个特征值全都简单，所以该块只能是

$$
\operatorname{span}\{q,x_{\lambda_+(h_i)},x_{-r}\},
\tag{224.12}
$$

稳定特征向量仍以 $q^{\mathsf T}x_\nu=1$ 归一。正 $q$ 规范的交织等距唯一：它把局部核向量送到 $q$，又必须把每个局部归一特征向量送到唯一的 $x_\nu$。这三个向量构成基。因此尖锐节点的实际实向量被强制为

$$
\psi_i=U_i(\sqrt{h_i},0,\sqrt{1-h_i})^{\mathsf T},
\tag{224.13}
$$

其新增坐标为零；不能再独立翻转负特征方向的符号。

令 $n=\delta x_{-r}$。Gram 恒等式使其为单位向量，且 $q^{\mathsf T}n=\delta>0$。规范节点在该方向的投影可精确计算为

$$
d(h):=\langle n,\psi_h\rangle
=\frac{\sqrt{1-h}\,[1+b(h)-r^2-2ar]}
       {(1+b(h))\sqrt{1-r^2}}.
\tag{224.14}
$$

为核对这一公式，使用局部预解式 $y_-=(I+rT_0)^{-1}f$。由第211.24式及负特征值关系，
$\det(I+rB_0)=(1+b(h))(1-r^2)$，并且

$$
\sqrt h\,(y_-)_1
=-\frac{r\sqrt{1-h}\,[2a-rb(h)]}
        {(1+b(h))(1-r^2)}.
\tag{224.15}
$$

与节点向量配对再乘 $\delta$ 即得（224.14）；这里只用规范压缩关系。

在第一个节点，（224.5）给出
$1-r^2+r(\lambda-9/10)<-1/400$；第三个节点则有
$1-r^2+r(\mu-9/10)>9/100$。根区间还给出
$\sqrt{1-h_1}>1/3$、$\sqrt{1-h_3}>1/100$，而两个分母都小于 $1/250$。因此

$$
d(h_1)<-\frac5{24},\qquad d(h_3)>\frac9{40}.
\tag{224.16}
$$

最后将这个投影符号转成第四坐标的符号。把（224.6）写为
$V=\begin{psmallmatrix}R&\delta z_3\\0&-r\end{psmallmatrix}$，$\|z_3\|=1$；写 $n=(v,\nu)$，则
$(R+rI)v=-\delta z_3\nu$。有 $\|R+rI\|<2$，且
$\det(R+rI)=r(r+\lambda)(r+\mu)>2$，所以最小奇异值大于 $1/2$，$\|v\|<2\delta$。置 $\epsilon=\operatorname{sign}\nu$，得到

$$
\|n-\epsilon e_4\|<4\delta<\frac1{100}.
\tag{224.17}
$$

结合（224.16），两个被强制的节点分别满足
$\epsilon(\psi_1)_4<0$、$\epsilon(\psi_3)_4>0$。

若存在题设实 $C^1$ 精确纯态曲线，则因 $p<1$，其连续正 $q$ 代表可全局写为 $\psi(p)=\rho(p)q/\sqrt{1-p}$。两个节点的第四坐标异号，故在其间某处必为零。但 $h_1>17/20>4/5$，这与（224.11）矛盾。证毕。

**注记 224.3（阻碍的精确作用域）。** 反例的根因是指定尖锐状态被落在一个不能穿越的实超平面两侧。它排除了同一个 $T\oplus(+1)$ 处理器中的所有实 $C^1$ 精确续接，包括允许中间奇异点的续接；不依赖某一种局部拼接算法失败。它没有排除复相位连接、其他五维处理器或负单位方向的扩张，亦不把该反例当作一般纯态最小维数的下界。结合第223节，同一四维共同处理器增加一个负单位方向后却能完成所需的实解析纯态续接。因此这里得到两份同为五维、却对同一个指定集合给出不同续接能力的程序：维数是同一个粗读数，新增方向参与约束的方式才区分它们。

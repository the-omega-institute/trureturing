## 1. 对象类型、关系记录与可辨识性

### 1.1. 类型与几何解释

项目五模式记为
$$
 \Sigma=(0,1,2,3,13)
 =(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]).
$$
在固定合法占位模型中，$0$ 是空占位事件；
在另供的 $\mathbb C^5$ 模型中，$|0\rangle$ 是范数一的基向量。
二者都不是未经解释就得到的物理空间原点。
关系丛卷第 3.1、3.4 条明确区分这些对象 [B]。

**定义 1.1（五模式的几何解释）。**

选择一个三维欧氏关系模型及映射
$$
 \iota:\Sigma\longrightarrow\mathbb R^3,\qquad
 \iota(0)=o,\quad \iota(i)=p_i\ (i=1,2,3),\quad \iota(13)=d.
$$
称 $o$ 为此解释中的内生原点。
正交原子要求 $v_i=p_i-o$ 非零且两两正交。
此处研究的一个闭合律是
$$
 d=p_1+p_3-o,\qquad d-o=v_1+v_3.
$$
该闭合律和欧氏模型属于所声明的解释，不能由五个名称单独取得。

项目完整五点函数代数包含独立系数
$f_2-f_0$ 与 $f_{13}-f_1-f_3+f_0$。
因此，“$F[2]$ 约束 $F[1,3]$”应通过具体相容律、耦合或传播规则实现；
不能只凭模式标签把两个函数系数识别 [B]。
后文给出的双井与失谐图正是两种可检查的实现。

### 1.2. 观察纤维不自动指定概率或相位

**定义 1.2（观察纤维与目标辨识）。**

令 $\mathcal C$ 为已经指定的候选配置集合，
$\pi:\mathcal C\to\mathcal Y$ 为实际记录映射。
若群 $G$ 作用在 $\mathcal C$ 且 $\pi(gc)=\pi(c)$，
允许将真正属于同一物理状态的规范副本取商。群作用必须保持候选集合；固定端点的纤维只允许保持那些端点条件的作用，或在同时运输端点数据的配置族上取商。
对记录 $y$，定义
$$
 \mathcal F_y=\pi^{-1}(y)/G.
$$
一个目标 $R:\mathcal C\to Z$ 可由记录唯一辨识，
指存在 $\bar R:\pi(\mathcal C)\to Z$ 使 $R=\bar R\circ\pi$；
使用商时，另要求 $R$ 在规范轨道上不变。

**命题 1.3（几何解释中的辨识、共同误差与协变接口）。**
在定义 1.1–1.2 的候选域、实际记录和规范条件下，关系目标可辨识当且仅当其在非空记录纤维上为常值。分支投影不能决定相干，整体坐标变换不能制造预测变化；共同误差抵消仅按以下域与相关性条件成立。

**证明。**
以下分别使用集合论因子化、二阶矩恒等式及酉函数演算，作为该指定关系接口的中间步骤；记录与合法未来的区别采用 [O] §1–2，类型与相干载体采用 [B] §3.1、3.4，Gram 标架采用 [G] 定义 2.1、假设 2.2 及推论 10.6。

**中间计算 1.3（预测唯一性的充要条件）。**

$R$ 能因子化为 $\bar R\circ\pi$，
当且仅当它在每个非空记录纤维上为常值。

计算：

若已因子化，则 $\pi(c)=\pi(c')$ 蕴含
$R(c)=\bar R(\pi(c))=\bar R(\pi(c'))=R(c')$。
反向，对每个非空纤维把其共同值定义为 $\bar R(y)$；
纤维上的常值性保证良定义。若要求 $\bar R$ 定义在整个 $\mathcal Y$ 上，则还须能在 $\mathcal Y\setminus\pi(\mathcal C)$ 上选定一个 $Z$ 值；当该补集非空且 $Z=\varnothing$ 时，扩张不存在。特别地 $\mathcal C=\varnothing,Z=\varnothing,\mathcal Y\ne\varnothing$ 是全域扩张的反例。若补集为空，或 $Z$ 非空，则分别直接定义，或用任取的一个 $z_0\in Z$ 常值扩张。

此定理允许当前记录不能确定观察者的完整来源，
但仍能准确确定某些关系目标。
“所有自身属性都不确定”不是这个定理的前提或结论。
项目观察者相对模型卷也分别固定候选集、记录和合法未来，
并展示当前读数相同但未来区别不同的模型 [O]。

**中间计算 1.4（同样的分支概率不能选出相干状态）。**

取正交单位向量 $|L\rangle,|R\rangle$，在其张成空间中令
$$
 \rho_{\rm mix}=\tfrac12(|L\rangle\langle L|+|R\rangle\langle R|),\qquad
 \rho_+=|+\rangle\langle +|,\quad
 |+\rangle=\frac{|L\rangle+|R\rangle}{\sqrt2}.
$$
二者对两个分支投影给出相同的概率 $(1/2,1/2)$，
但对 $X=|L\rangle\langle R|+|R\rangle\langle L|$ 的期望分别为 $0$ 和 $1$。
因而只给分支不确定性，不足以选定量子相干。

计算：

在 $(|L\rangle,|R\rangle)$ 基中，前者为 $I_2/2$，
后者为 $\frac12\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$。
其对角元相同，非对角元不同。与
$X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$
相乘取迹，得到所列值。

### 1.3. 不确定点与确定关系可以同时存在

**中间计算 1.5（共同平移和相对位移的区别）。**

共同平移
$$
 (o,p_1,p_2,p_3,d)\longmapsto
 (o+a,p_1+a,p_2+a,p_3+a,d+a)
$$
保持所有相对向量、成对距离、锚定 Gram 以及闭合律。
若只改变 $o$ 为 $o+\delta$ 而固定 $p_i$，则
$$
 g_{ij}(o+\delta)-g_{ij}(o)
 =-\delta\cdot(v_i+v_j)+\left\lVert \delta\right\rVert^2,\qquad
 g_{ij}(o)=v_i\cdot v_j.
 \tag{1.1}
$$
但 $v_i-v_j=p_i-p_j$ 仍精确保持。

计算：

共同平移在每个差向量中抵消。
只移动原点时，$v_i$ 变为 $v_i-\delta$，
展开 $(v_i-\delta)\cdot(v_j-\delta)$ 即得式 (1.1)；
两项相减则再次消去 $\delta$。

这与项目三轴几何卷中同源距离的标架自由一致：
固定锚点后的张成实现只差正交变换，未固定锚点时还允许整体平移；
若同时保持有符号叉积，则保持群在三维降为 $SO(3)$。
这些是表示自由，不能自动成为新的实际控制权限 [G]。

**中间计算 1.6（共同误差抵消）。**

对二阶矩有限的实随机变量，
$$
 \operatorname{Var}(X_i-X_0)=
 \operatorname{Var} X_i+\operatorname{Var} X_0-2\operatorname{Cov}(X_i,X_0).
 \tag{1.2}
$$
对于处于自伴算符 $A,B$ 共同定义域中的归一化纯态，差算符仅在共同域上使用，不假定 $A-B$ 自动自伴；
以二次型 $\operatorname{Var} A=\left\lVert \Delta A\psi\right\rVert^2$ 和
$\operatorname{Cov}(A,B)=\operatorname{Re}\langle\Delta A\psi,\Delta B\psi\rangle$
定义方差与协方差时也有同一恒等式。
当算符乘积有定义时，后者等于
$\frac12\langle\Delta A\Delta B+\Delta B\Delta A\rangle$。

计算：

将中心化差 $\Delta X_i-\Delta X_0$ 的平方展开取期望；
算符情形保留两个交叉项，其和正是对称协方差的两倍。

例如在经典共同噪声模型中，$r_i,r_0$ 为固定常数，$X_i=A+r_i$、$X_0=A+r_0$，
无论 $\operatorname{Var} A$ 多大，$X_i-X_0=r_i-r_0$ 都完全确定。
在量子模型中，宽的质心波包也可以与窄的相对波包并存；
第 4 节将给出它们的精确动力学分离。

**中间计算 1.7（坐标协变不能制造观测变化）。**

设 $\rho$ 为迹一正迹类算符、$E$ 为有界效果、$H$ 为自伴算符。若一个表示变换同时运输
$$
 \rho'=U\rho U^\dagger,\quad
 H'=UHU^\dagger,\quad E'=UEU^\dagger
$$
且 $U$ 为酉算符，则任意时间的读数满足
$$
 \operatorname{Tr}\!\left(E'e^{-itH'/\hbar}\rho'e^{itH'/\hbar}\right)
 =
 \operatorname{Tr}\!\left(Ee^{-itH/\hbar}\rho e^{itH/\hbar}\right).
$$

计算：

函数演算给 $e^{-itH'/\hbar}=Ue^{-itH/\hbar}U^\dagger$。
代入后相邻 $U^\dagger U$ 抵消，最后用迹的循环性。

证毕。

## 2. 内生原点的镜像完成与稳定性

本节把项目中三路结构的讨论 [G]写成一个明确的欧氏实现模型。
这里的三维实内积空间、点的实现、内积读出与五点闭合式，都是本节明示的数学条件；
以下定理不声称这些条件已经由裸符号标签自动推出，也不把几何上的不可辨识直接解释为量子叠加。
在这些条件下，原点的不确定性、关系的稳定性以及突然改变的读出，确实可以作出严格区分。

### 2.1. 三条正交腿的原点分类

**定义 2.1（正交原点与五点完成）。**

设 $p_1,p_2,p_3\in\mathbb R^3$ 是三个不共线的固定端点；固定端点是本节几何模型的显式前提，稳定读数则是给定记录映射对演化取值不变的另一个条件，前者不推出模式天然稳定。
其仿射平面记为 $\Pi=\operatorname{aff}\{p_1,p_2,p_3\}$。
对候选观察者原点 $o\in\mathbb R^3$，定义三条腿与三个正交残差
$$
 v_i(o)=p_i-o,\qquad
 g_{ij}(o)=\langle p_i-o,p_j-o\rangle\quad(1\leq i<j\leq3).
$$
若全部 $g_{ij}(o)=0$，则称 $o$ 为正交原点；若再有全部 $v_i(o)\ne0$，
则称其为非退化正交原点。
选定闭合式
$$
 d(o)=p_1+p_3-o,
$$
并将有序五元组 $\mathcal A(o)=(o,p_1,p_2,p_3,d(o))$ 称为相应的五点完成。
该闭合式是本节采用的具体关系规则，并非两端点标签本身的必然含义。

**命题 2.2（正交原点分类在五点软相融能量中的应用）。**

在定义 2.1 中给定 $k>0$，平方罚函数 $\frac k2\sum_{i<j}g_{ij}(o)^2$ 的零点就是下述原点分类给出的全部完成。在严格锐角情形，其法向限制是 $\frac{3k}{2}(q^2-h^2)^2$；分类中的 $h,H$ 因而直接确定这份软相融能量的井间距与法向屏障。

**证明。**
平方和为零当且仅当每个残差为零。所需原点分类的参数与完整推导如下；距离—Gram 对应使用 [G] 定义 2.1 的同源标定。

令 $s_{ij}=\left\lVert p_i-p_j\right\rVert^2$，并对 $\{i,j,k\}=\{1,2,3\}$ 定义
$$
 \alpha_i=\frac{s_{ij}+s_{ik}-s_{jk}}2.
 \tag{2.1}
$$
存在非退化正交原点，当且仅当
$$
 \alpha_1>0,\qquad\alpha_2>0,\qquad\alpha_3>0;
$$
等价地，端点三角形为严格锐角三角形。
在此条件下，定义
$$
 S=\sum_{i=1}^3\alpha_i^{-1},\qquad
 h^2=S^{-1},\qquad
 w_i=\frac{\alpha_i^{-1}}{S}=\frac{h^2}{\alpha_i},\qquad
 H=\sum_{i=1}^3w_ip_i.
 \tag{2.2}
$$
则 $H$ 恰为端点三角形的垂心。对 $\Pi$ 的任一单位法向量 $n$，
全部非退化正交原点恰为
$$
 o_-=H-hn,\qquad o_+=H+hn.
 \tag{2.3}
$$
两原点相距 $2h$，且在任一原点处均有
$$
 \left\lVert p_i-o_\pm\right\rVert^2=\alpha_i.
$$
若端点三角形为直角三角形，则唯一正交原点是直角顶点，且有一条腿为零；
若为钝角三角形，则不存在正交原点。

原点分类计算：由余弦恒等式，
$$
 \alpha_i=\langle p_j-p_i,p_k-p_i\rangle,
 \qquad s_{ij}=\alpha_i+\alpha_j.
$$
所以 $\alpha_i$ 的符号正是第 $i$ 个内角余弦的符号。
若 $o$ 是正交原点，则
$$
 s_{ij}=\left\lVert v_i(o)-v_j(o)\right\rVert^2
       =\left\lVert v_i(o)\right\rVert^2+\left\lVert v_j(o)\right\rVert^2.
$$
联立这三个等式得到 $\alpha_i=\left\lVert v_i(o)\right\rVert^2$。
非退化情形下全部 $\alpha_i>0$，证明了必要性。

下面假设全部 $\alpha_i>0$，构造全部解。
式(2.2)给出 $w_i>0$、$\sum_iw_i=1$ 与
$w_i\alpha_i=h^2$。令 $r_i=p_i-H$。
对任何权重和为一的点组，直接展开平方可得加权方差恒等式
$$
 B:=\sum_jw_j\left\lVert p_j-H\right\rVert^2
   =\sum_{i<j}w_iw_j\left\lVert p_i-p_j\right\rVert^2,
$$
以及
$$
 \sum_jw_j\left\lVert p_i-p_j\right\rVert^2=\left\lVert p_i-H\right\rVert^2+B.
$$
本例中
$$
 B=\sum_iw_i\alpha_i(1-w_i)=2h^2,
$$
且
$$
 \sum_jw_j s_{ij}
 =\alpha_i(1-w_i)+\sum_{j\ne i}w_j\alpha_j
 =\alpha_i+h^2.
$$
因此
$$
 \left\lVert r_i\right\rVert^2=\alpha_i-h^2,\qquad
 \langle r_i,r_j\rangle=-h^2\quad(i\ne j).
 \tag{2.4}
$$
第二式由第一式和 $\left\lVert r_i-r_j\right\rVert^2=s_{ij}=\alpha_i+\alpha_j$ 得出。
于是对互不相同的 $i,j,k$，
$$
 \langle p_i-H,p_j-p_k\rangle
 =\langle r_i,r_j-r_k\rangle=0.
$$
又 $H\in\Pi$，故 $H$ 同时位于三条高上，确为垂心。

由于 $r_i\perp n$，对 $o_\pm=H\pm hn$ 有
$$
 \langle p_i-o_\pm,p_j-o_\pm\rangle
 =\langle r_i,r_j\rangle+h^2=0\quad(i\ne j),
$$
并有 $\left\lVert p_i-o_\pm\right\rVert^2=\left\lVert r_i\right\rVert^2+h^2=\alpha_i>0$。
这证明所给两个点都是非退化正交原点。

为证完备性，任取一个非退化正交原点 $o$。
前述必要性已给出 $\left\lVert v_i(o)\right\rVert^2=\alpha_i$。
由于 $H-o=\sum_iw_iv_i(o)$，对任意 $i\ne j$，
$$
 \langle H-o,p_i-p_j\rangle
 =w_i\alpha_i-w_j\alpha_j=0.
$$
因此 $H-o\perp\Pi$。同时，利用三条腿的正交性，
$$
 \left\lVert H-o\right\rVert^2=\sum_iw_i^2\alpha_i
 =h^4\sum_i\alpha_i^{-1}=h^2.
$$
故 $o$ 只能是式(2.3)中的两个点。

若某个 $\alpha_i<0$，必要条件 $\alpha_i=\left\lVert v_i(o)\right\rVert^2$ 排除所有解。
若 $\alpha_i=0$，任何解必须满足 $o=p_i$；此时
$\langle p_j-p_i,p_k-p_i\rangle=\alpha_i=0$，所以该点确实是唯一解，
且第 $i$ 条腿为零。三点不共线排除了两个顶点同时为直角的情形。
由此完成全部分类。再用 $r_i\perp n$ 与 $r_i\cdot r_j=-h^2$，得到 $g_{ij}(H+qn)=q^2-h^2$；三项平方相加即给所述法向能量。

证毕。

本节下文除另有说明外，均在 $\alpha_i>0$ 的非退化情形工作。
式(2.2)中的 $h$ 是由关系数据决定的镜像高度，
并非任意加入的几何尺度。

### 2.2. 镜像不可辨识与规范选择

**定理 2.3（两个五点完成具有相同的全部距离）。**

令 $d_\pm=p_1+p_3-o_\pm$。
关于平面 $\Pi$ 的反射固定 $p_1,p_2,p_3$，并分别交换
$o_-\leftrightarrow o_+$ 与 $d_-\leftrightarrow d_+$。
因此，两个有序五点完成的所有十个成对距离完全相同。
这些距离的平方具体为
$$
\begin{aligned}
 \left\lVert o_\pm-p_i\right\rVert^2&=\alpha_i,
 &\left\lVert p_i-p_j\right\rVert^2&=\alpha_i+\alpha_j\quad(i<j),\\
 \left\lVert d_\pm-o_\pm\right\rVert^2&=\alpha_1+\alpha_3,
 &\left\lVert d_\pm-p_1\right\rVert^2&=\alpha_3,\\
 \left\lVert d_\pm-p_3\right\rVert^2&=\alpha_1,
 &\left\lVert d_\pm-p_2\right\rVert^2&=\alpha_1+\alpha_2+\alpha_3.
 \tag{2.5}
\end{aligned}
$$
故任何只依赖这些距离的读出都无法区分这两个完成。

**证明。**

反射映射为
$$
 T(x)=x-2\langle x-H,n\rangle n.
$$
它是固定 $\Pi$ 的仿射等距映射，且 $T(o_+)=o_-$。
仿射性以及闭合式中系数之和 $1+1-1=1$ 给出
$$
 T(d_+)=T(p_1+p_3-o_+)=p_1+p_3-o_-=d_-.
$$
故全部对应距离相等。为直接验证式(2.5)，
在任一正交原点处写 $d=o+v_1+v_3$，
再利用 $\langle v_i,v_j\rangle=0$ 与 $\left\lVert v_i\right\rVert^2=\alpha_i$ 即可。

证毕。

**定义 2.3a（规范商与手性读口）。**
若把包括反射在内的所有欧氏等距变换均视为规范变换，
则两个镜像完成在相应商空间中是同一状态的两个代表。
若只把保持定向的刚体变换视为规范，并把手性作为可观测关系，
则两者可成为不同状态。
事实上，一个保持定向的刚体变换若逐点固定三个不共线端点，就只能是恒等变换，
因而不能交换两个原点。
所以在讨论两支之间的转移之前，必须先说明所采用的规范群和可取得的关系读出。

**命题 2.4（共同平移与相对原点误差）。**

对全部五点施加同一个平移不改变腿向量、成对距离、内积或手性。
若固定三个端点，只把 $o$ 改为 $o+\delta$，则
$$
\begin{aligned}
 v_i(o+\delta)&=v_i(o)-\delta,\\
 g_{ij}(o+\delta)&=g_{ij}(o)
 -\langle\delta,v_i(o)+v_j(o)\rangle+\left\lVert \delta\right\rVert^2,\\
 d(o+\delta)&=d(o)-\delta.
 \tag{2.6}
\end{aligned}
$$
特别地，当 $\left\lVert \delta\right\rVert\leq\varepsilon_o$ 时，
$$
 |g_{ij}(o+\delta)-g_{ij}(o)|
 \leq\varepsilon_o\bigl(\left\lVert v_i(o)\right\rVert+\left\lVert v_j(o)\right\rVert\bigr)+\varepsilon_o^2.
$$
但 $v_i(o+\delta)-v_j(o+\delta)=p_i-p_j$ 始终不变。

**证明。**

共同平移在点差中相消；相对原点误差的三个恒等式由定义直接展开。
最后的不等式由柯西--施瓦茨不等式得到。

证毕。

因此，原点未知并不意味着所有关系独立地变成未知。
在本闭合模型中，$o$ 与 $d$ 的变化严格反向相关，
而 $o+d=p_1+p_3$ 保持精确成立。

### 2.3. 法向残差、分辨率与分支合并

**命题 2.5（法向线上三条残差相同）。**

在法向线上取 $o(q)=H+qn$，其中 $q\in\mathbb R$。
则对所有 $i<j$，
$$
 g_{ij}(o(q))=q^2-h^2.
 \tag{2.7}
$$
因此法向线上的精确正交原点恰为 $q=\pm h$。

**证明。**

由式(2.4)与 $r_i\perp n$，
$$
 g_{ij}(o(q))=\langle r_i-qn,r_j-qn\rangle
 =-h^2+q^2.
$$

证毕。

**定义 2.6（有限分辨率的相融集）。**

给定逐项内积残差容差 $\varepsilon\geq0$，定义
$$
 S_\varepsilon
 =\{q\in\mathbb R:|g_{ij}(o(q))|\leq\varepsilon\text{ 对全部 }i<j\}
 =\{q\in\mathbb R:|q^2-h^2|\leq\varepsilon\}.
$$
这里 $\varepsilon$ 的量纲是长度平方；它与位置误差半径 $\varepsilon_o$ 不同。

**定理 2.7（相融集的精确连通阈值）。**

若 $0\leq\varepsilon<h^2$，则
$$
 S_\varepsilon=
 [-\sqrt{h^2+\varepsilon},-\sqrt{h^2-\varepsilon}]
 \;\cup\;
 [\sqrt{h^2-\varepsilon},\sqrt{h^2+\varepsilon}],
$$
恰有两个连通分支。
若 $\varepsilon\geq h^2$，则
$$
 S_\varepsilon=[-\sqrt{h^2+\varepsilon},\sqrt{h^2+\varepsilon}],
$$
是一个连通区间。

**证明。**

定义中的不等式等价于
$$
 \max\{0,h^2-\varepsilon\}\leq q^2\leq h^2+\varepsilon.
$$
当下界为正时，正负平方根给出两个互不相交的闭区间；
当下界为零时，两区间在零点接通。

证毕。

该阈值描述的是允许误差下的可行集拓扑。
它既不规定系统如何运动，也不为从一支到另一支的运动赋予任何概率。

**推论 2.8（平方根反演的稳定范围）。**

若 $0\leq\varepsilon<h^2$ 且 $q$ 位于 $S_\varepsilon$ 的正分支，则
$$
 |q-h|\leq\frac{\varepsilon}{h+\sqrt{h^2-\varepsilon}}\leq\frac{\varepsilon}{h}.
$$
若写 $\lambda=h^2$，精确两支为 $q_\pm(\lambda)=\pm\sqrt\lambda$。
其反演导数在 $\lambda>0$ 时为
$$
 \frac{dq_\pm}{d\lambda}=\pm\frac1{2\sqrt\lambda}.
$$
在任意 $[0,L]$、$L>0$ 上，平方根没有统一有限的 Lipschitz 常数，
但满足
$$
 |\sqrt\lambda-\sqrt{\lambda'}|\leq\sqrt{|\lambda-\lambda'|}.
$$

**证明。**

第一式来自 $|q-h|=|q^2-h^2|/(q+h)$ 及
$q\geq\sqrt{h^2-\varepsilon}$。
对平方根有理化即可得到差商公式与上述平方根界。
取 $\lambda=0$、$\lambda'=a^2$，其 Lipschitz 比值为 $1/a$，
随 $a\downarrow0$ 发散。

证毕。

### 2.4. 法向读出的敏感性与手性阈值

**命题 2.9（单位法向的条件数界）。**

固定不同的 $p_1,p_3$，定义
$$
 N(o)=(p_1-o)\times(p_3-o),\qquad A=\left\lVert N(o)\right\rVert.
$$
若 $A>0$，且
$$
 \left\lVert \delta\right\rVert\leq\varepsilon_o,\qquad
 \eta=\left\lVert p_3-p_1\right\rVert\varepsilon_o<A,
$$
则 $N(o+\delta)\ne0$，并有
$$
 \left\|\frac{N(o+\delta)}{\left\lVert N(o+\delta)\right\rVert}-
 \frac{N(o)}{A}\right\|
 \leq\frac{2\eta}{A}.
 \tag{2.8}
$$

**证明。**

叉积双线性与 $\delta\times\delta=0$ 给出精确恒等式
$$
 N(o+\delta)=N(o)+(p_3-p_1)\times\delta.
$$
故扰动范数不超过 $\eta$，且新法向的范数至少为 $A-\eta>0$。
一般地，若 $y=x+e$、$\left\lVert x\right\rVert=A>0$、$y\ne0$，则
$$
 \frac{y}{\left\lVert y\right\rVert}-\frac{x}{A}
 =\frac{y-x}{A}+y\left(\frac1{\left\lVert y\right\rVert}-\frac1A\right).
$$
由反三角不等式，其范数不超过 $2\left\lVert e\right\rVert/A$。
代入 $x=N(o)$、$y=N(o+\delta)$ 即得结论。

证毕。

$A$ 是三角形 $(o,p_1,p_3)$ 面积的两倍。
因此，面积远离零时单位法向稳定；接近共线时，归一化法向的误差界会失去控制。

**命题 2.10（连续位置引起单位法向翻转）。**

取
$$
 p_1=(-1,0,0),\qquad p_3=(1,0,0),\qquad o(u)=(0,u,0).
$$
则
$$
 N(o(u))=(0,0,2u),\qquad
 \frac{N(o(u))}{\left\lVert N(o(u))\right\rVert}=\operatorname{sgn}(u)(0,0,1)
 \quad(u\ne0).
$$
原点和未归一化的面积向量连续，而单位法向在退化位置 $u=0$ 两侧相反。
这说明读出符号可在连续几何变化中出现突变。
该例展示一般配置空间中法向读出的退化，不声称整条路径满足三条精确正交约束。

**证明。** 两腿为 $(-1,-u,0)$ 与 $(1,-u,0)$，按叉积逐项展开得到 $(0,0,2u)$；其范数是 $2|u|$。除以范数就给所列符号，$u=0$ 时叉积为零，单位法向没有定义。证毕。

**命题 2.11（手性符号的精确位置误差阈值）。**

令
$$
 A_\Pi=(p_3-p_1)\times(p_2-p_1),\qquad
 D(o)=\det(p_1-o,p_3-o,p_2-o).
$$
此处手性统一按标签次序 $(1,3,2)$ 定义。
则
$$
 D(o)=\langle A_\Pi,p_1-o\rangle,\qquad
 D(o+\delta)=D(o)-\langle A_\Pi,\delta\rangle.
$$
若 $D(o)\ne0$，误差球 $\left\lVert \delta\right\rVert\leq\varepsilon_o$ 内全部点都保持相同的严格手性符号，
当且仅当
$$
 \varepsilon_o<\frac{|D(o)|}{\left\lVert A_\Pi\right\rVert}
 =\operatorname{dist}(o,\Pi).
$$
等号时误差球触及零手性平面；严格大于时误差球包含两种手性。
在 $o=o_\pm$ 处，该距离恰为 $h$。

**证明。**

在行列式的第二、第三列分别减去第一列，得到 $D(o)$ 的所示表达式。
沿 $A_\Pi/\left\lVert A_\Pi\right\rVert$ 的方向移动时，$D$ 以最大绝对斜率
$\left\lVert A_\Pi\right\rVert$ 改变。
柯西--施瓦茨不等式给出误差球内的上下界，且沿该方向可以达到这些界。
故上述条件既充分又必要。

证毕。

### 2.5. 完整三维残差的局部稳定证书

**定理 2.12（非退化支内的小残差控制原点误差）。**

定义
$$
 C(o)=\bigl(g_{12}(o),g_{13}(o),g_{23}(o)\bigr)^{\mathsf T}.
$$
设 $o_*$ 是任一非退化正交原点，$v_i=p_i-o_*$，并令
$$
 a_{\min}=\min_i\sqrt{\alpha_i}>0,\qquad
 a_{\max}=\max_i\sqrt{\alpha_i}.
$$
雅可比 $J=DC(o_*)$ 的三行为
$-(v_1+v_2)^{\mathsf T}$、$-(v_1+v_3)^{\mathsf T}$ 与
$-(v_2+v_3)^{\mathsf T}$。
它满足
$$
 \sigma_{\min}(J)\geq a_{\min},\qquad
 \sigma_{\max}(J)\leq2a_{\max},\qquad
 |\det J|=2\sqrt{\alpha_1\alpha_2\alpha_3}>0.
 \tag{2.9}
$$
对任意 $\delta\in\mathbb R^3$ 有精确展开
$$
 C(o_*+\delta)=J\delta+\left\lVert \delta\right\rVert^2\mathbf1,
 \qquad\mathbf1=(1,1,1)^{\mathsf T}.
 \tag{2.10}
$$
若 $\left\lVert \delta\right\rVert\leq a_{\min}/(2\sqrt3)$，则
$$
 \left\lVert C(o_*+\delta)\right\rVert\geq\frac{a_{\min}}2\left\lVert \delta\right\rVert.
 \tag{2.11}
$$
因此，在该已选局部邻域内，$\left\lVert C(o)\right\rVert\leq\zeta$ 蕴含
$\left\lVert o-o_*\right\rVert\leq2\zeta/a_{\min}$。

**证明。**

在正交单位基 $e_i=v_i/\sqrt{\alpha_i}$ 中，记
$$
 B=\begin{pmatrix}1&1&0\\1&0&1\\0&1&1\end{pmatrix},\qquad
 D_\alpha=\operatorname{diag}(\sqrt{\alpha_1},\sqrt{\alpha_2},\sqrt{\alpha_3}).
$$
则 $J=-BD_\alpha$，从而
$$
 J^{\mathsf T}J=D_\alpha(I+\mathbf1\mathbf1^{\mathsf T})D_\alpha.
$$
矩阵 $I+\mathbf1\mathbf1^{\mathsf T}$ 的本征值是 $4,1,1$。
因此对每个 $x$，
$$
 a_{\min}^2\left\lVert x\right\rVert^2
 \leq x^{\mathsf T}J^{\mathsf T}Jx
 \leq4a_{\max}^2\left\lVert x\right\rVert^2,
$$
得到奇异值界；由 $|\det B|=2$ 得到行列式公式。
式(2.10)来自
式(2.6)与 $C(o_*)=0$。
最后，反三角不等式给出
$$
 \left\lVert C(o_*+\delta)\right\rVert
 \geq a_{\min}\left\lVert \delta\right\rVert-\sqrt3\left\lVert \delta\right\rVert^2.
$$
施加所给半径条件即得式(2.11)。

证毕。

非零雅可比行列式还允许应用逆函数定理，在每个镜像原点附近分别取得唯一的局部反演。
这里的局部唯一性不能消除全局的两支歧义：两个原点都满足 $C(o)=0$。
当某条腿趋于零时，上述稳定证书退化；
由 $h^2=(\sum_i\alpha_i^{-1})^{-1}\leq\min_i\alpha_i$，镜像高度也随之趋于零。

### 2.6. 关系罚函数与完整配置空间中的屏障

**定义 2.13（平方残差罚函数）。**

对 $k>0$，定义完整三维配置空间上的非负函数
$$
 V_{\mathrm{full}}(o)=\frac{k}{2}\sum_{i<j}g_{ij}(o)^2.
$$
这里把关系违背赋予能量代价，是模型选择；若坐标有长度单位，则 $g_{ij}$ 的单位为长度平方，$k$ 的单位为能量除以长度四次方。

**命题 2.14（法向限制给出四次双井形状）。**

$V_{\mathrm{full}}$ 恰在 $o_\pm$ 处取零。
在法向限制 $o(q)=H+qn$ 下，
$$
 V(q):=V_{\mathrm{full}}(H+qn)
 =\Lambda(q^2-h^2)^2,\qquad \Lambda=\frac{3k}{2}.
 \tag{2.12}
$$
该限制函数的两个最小点为 $q=\pm h$，其中点屏障高度为 $\Lambda h^4$。

**证明。**

平方和为零当且仅当全部正交残差为零，原点分类定理给出全部零点。
再把式(2.7)代入平方和，即得四次式。
在 $[-h,h]$ 上，该式在 $q=0$ 达到最大值 $\Lambda h^4$。

证毕。

式(2.12)提供了可与另行指定的动力学相接的势能候选。
其法向屏障不能自动用作允许横向运动时的完整屏障；
以下例子给出严格反例和精确的完整屏障值。

**命题 2.15（三个坐标端点的完整屏障恰为 $k/8$）。**

取长度单位为一，$p_i=e_i$ 为 $\mathbb R^3$ 的标准单位基。若恢复物理长度 $\ell>0$、取 $p_i=\ell e_i$，下述势能整体乘 $\ell^4$，故完整屏障与法向屏障分别为 $k\ell^4/8$ 与 $k\ell^4/6$。以下公式仍取 $\ell=1$；此时
$$
 \alpha_1=\alpha_2=\alpha_3=1,\quad
 H=\frac13(1,1,1),\quad
 h=\frac1{\sqrt3},\quad
 n=\frac1{\sqrt3}(1,1,1),
$$
且 $o_-=0$、$o_+=\frac23(1,1,1)$。
将任意原点唯一写成
$$
 o=H+qn+y,\qquad y\perp n,\qquad r^2=\left\lVert y\right\rVert^2.
$$
则
$$
 V_{\mathrm{full}}(o)
 =\frac{k}{2}\left[3\left(q^2+r^2-\frac13\right)^2+r^2\right].
 \tag{2.13}
$$
定义连接两个最小点的最小最大高度
$$
 \mathcal B=\inf_{\substack{\gamma\in C([0,1],\mathbb R^3)\\
                         \gamma(0)=o_-,\ \gamma(1)=o_+}}
             \max_{s\in[0,1]}V_{\mathrm{full}}(\gamma(s)).
$$
则
$$
 \mathcal B=\frac{k}{8}<\frac{k}{6}=V(0).
 \tag{2.14}
$$

**证明。**

若 $\{i,j,\ell\}=\{1,2,3\}$，由 $y_1+y_2+y_3=0$ 直接计算得
$$
 g_{ij}(o)=\left\lVert o\right\rVert^2-o_i-o_j
 =q^2+r^2-\frac13+y_\ell.
$$
平方后求和，含 $\sum_\ell y_\ell$ 的交叉项消失，得到
式(2.13)。

对任何允许的连续路径，法向坐标 $q$ 从 $-h$ 变到 $h$，
故由介值定理至少一次通过 $q=0$。
在该截面令 $z=r^2\geq0$，则
$$
 3\left(z-\frac13\right)^2+z
 =3\left(z-\frac16\right)^2+\frac14\geq\frac14.
$$
因此每条连接路径的最大势能都至少为 $k/8$。

反过来，在 $\Pi$ 的方向空间中固定任一单位向量 $e\perp n$，取
$$
 r(q)=\sqrt{\max\left\{0,\frac16-q^2\right\}},\qquad
 \widetilde\gamma(q)=H+qn+r(q)e,
 \qquad -\frac1{\sqrt3}\leq q\leq\frac1{\sqrt3}.
$$
这是连续路径，两个端点分别是 $o_-$ 与 $o_+$。
在 $|q|\leq1/\sqrt6$ 时，其平方残差和为
$$
 3\left(q^2+r(q)^2-\frac13\right)^2+r(q)^2
 =\frac14-q^2\leq\frac14.
$$
在 $1/\sqrt6\leq|q|\leq1/\sqrt3$ 时，$r(q)=0$，相应值为
$$
 3\left(q^2-\frac13\right)^2\leq\frac1{12}.
$$
因此该路径上的势能始终不超过 $k/8$，且在 $q=0$ 达到此值。
将参数区间线性重参数化为 $[0,1]$，它即属于定义 $\mathcal B$ 的路径族，
从而得到匹配的上界。
法向线的中点则有 $r=0$、$q=0$，其势能为 $k/6$。

证毕。

这里求得的是所有连续路径中的最小最大势能高度。
所构造的路径不必在拼接点可微，也未被证明最小化任何动力学作用量；
连续性已经足够完成上述高度定理。
若另行研究量子运动或半经典作用量，必须使用实际允许的配置空间与动能，
不能沿用未经横向约束的法向单变量结论。

### 2.7. 无向法线的全局选向障碍

**命题 2.16（仅无向法线输入下的镜像原点选择）。**

固定 $H\in\mathbb R^3,h>0$，若输入只保留无向单位法线 $[n]=\{n,-n\}\in\mathbb{RP}^2$，则不能连续地为每个输入选择完成 $H+hn,H-hn$ 之一。因为这样的选择减去 $H$ 再除以 $h$，就会给出以下不可能的全局选向：不存在连续映射 $s:\mathbb{RP}^2\to S^2$，使每个 $[n]$ 都满足
$s([n])\in\{n,-n\}$。

**证明。**

考虑 $\nu(\theta)=(\cos\theta,\sin\theta,0)$，$0\leq\theta\leq\pi$。
若存在所述 $s$，则
$$
 \epsilon(\theta)=\langle s([\nu(\theta)]),\nu(\theta)\rangle\in\{-1,1\}
$$
连续，故在该区间上为常数，且
$s([\nu(\theta)])=\epsilon(\theta)\nu(\theta)$。
但 $[\nu(0)]=[\nu(\pi)]$ 而 $\nu(\pi)=-\nu(0)$，
这要求同一个 $s$ 值同时等于两个相反的单位向量，矛盾。

证毕。

该命题只适用于输入确实只保留无向法线的读出。
若输入已保留有序的两条平面轴或额外定向信息，底空间和读出规则已经改变，
不能直接套用这一障碍。
它说明某些符号突变可以来自全局选向规则的接缝；
与局部条件数发散、镜像完成不可辨识及实际动力学转移，应分别识别。

## 3. 从相融残差到双井，以及势垒下的真实概率流

### 3.1. 必须明确的物理供应条件

沿用上一节的严格锐角三端点、垂心 $H$ 和高度 $h>0$。
这里的 $n$ 是端点平面 $\operatorname{aff}\{p_1,p_2,p_3\}$ 的单位法向，
一般不是另一个平面 $\operatorname{aff}\{o,p_1,p_3\}$ 的法向 $p_2-o$。
这里把允许的原点配置限制在法向线上：
$$
 o(q)=H+qn,\qquad q\in\mathbb R.
 \tag{3.1}
$$
这一限制是模型条件。一般三维软约束容许离轴路径，
其最低屏障可能比法向线上的屏障低，上一节给出了精确反例。

**定义 3.1（关系软约束能量）。**

令 $k>0$，将三项正交残差的平方赋为势能
$$
 V(q)=\frac{k}{2}\sum_{1\le i<j\le3}
 \bigl((p_i-o(q))\cdot(p_j-o(q))\bigr)^2.
 \tag{3.2}
$$
设 $\Lambda=3k/2$。这里的 $k$ 具有能量除以长度四次方的单位；
将一个相容损失指定为实际势能，是需要检验的物理模型条件。

**定理 3.2（正交残差产生四次双井）。**

在上述法向模型中，
$$
 \boxed{V(q)=\Lambda(q^2-h^2)^2.}
 \tag{3.3}
$$
势能仅在两个正交原点 $q=\pm h$ 取最小值零，
中点屏障为 $V_b=\Lambda h^4$，并有
$$
 V''(\pm h)=8\Lambda h^2,\qquad V''(0)=-4\Lambda h^2.
$$

**证明。**

上一节证明每个异指标残差都等于 $q^2-h^2$。
三项平方相加给式 (3.3)。直接微分
$V'=4\Lambda q(q^2-h^2)$ 和
$V''=4\Lambda(3q^2-h^2)$，得到全部结论。

证毕。

几何完成、能量赋值和量子动力学是三个不同步骤。
上述两个井还必须代表可区分的物理关系配置。
如果整个反射已经作为规范识别，两井只是同一状态的两个代表，
就不能把代表之间的改变叫作物理隧穿。
可以另给一个实际手性读口使两井可区分，
但不能同时把该手性值强制冻结为唯一允许扇区又要求它发生改变。

**定义 3.3（法向关系自由度的量子模型）。**

另供有效质量 $m>0$、$\hbar>0$、态空间 $L^2(\mathbb R,dq)$，
及正闭二次型
$$
 \mathfrak h[\psi]=
 \frac{\hbar^2}{2m}\int_{\mathbb R}|\psi'(q)|^2\,dq
 +\Lambda\int_{\mathbb R}(q^2-h^2)^2|\psi(q)|^2\,dq,
$$
$$
 \mathcal Q=
 \{\psi\in H^1(\mathbb R):(q^2-h^2)\psi\in L^2(\mathbb R)\}.
 \tag{3.4}
$$
由其 Friedrichs 实现定义自伴 Hamilton 算符
$$
 \widehat H_q=-\frac{\hbar^2}{2m}\frac{d^2}{dq^2}
                   +\Lambda(q^2-h^2)^2.
 \tag{3.5}
$$
概率按位置谱测度给出，演化为
$e^{-it\widehat H_q/\hbar}$。
这些是本节声明的量子结构，不是将认识上的不知道重新命名所得。

该表示算符的精确定义域可写为
$$
D(\widehat H_q)=\{\psi\in\mathcal Q:
-\hbar^2\psi''/(2m)+V\psi\in L^2(\mathbb R)
\text{（分布意义）}\}.
$$
这是闭型表示定理给出的弱定义域：若所列分布是 $f\in L^2$，先在 $C_c^\infty$ 上分部积分，再按型范数稠密性延到 $\mathcal Q$，便有 $\mathfrak h(\chi,\psi)=\langle\chi,f\rangle$；反向由该等式在测试函数上成立即得分布关系。这里 $C_c^\infty$ 的型稠密性由先截断再在紧集平滑取得。型域是式 (3.4) 中的交集，不是全部 $H^1(\mathbb R)$。
它包含紧支撑光滑函数，因而稠密；
在型范数中完备，因为 $H^1$ 极限和加权 $L^2$ 极限可由局部极限识别。
正闭二次型表示、自伴算符与极小极大原则的标准依据见
Teschl 的作者公开教材 [S]。
双井的通常物理解释见 Tong 的第 2.3.4 节 [T]；
以下将给出当前四次势的显式估计和概率流证明。

### 3.2. 两个低于势垒的能级

**定理 3.5（两个势垒下能级的显式充分条件）。**

记 $E_e=\inf_{\psi\in\mathcal Q,\|\psi\|=1}\mathfrak h[\psi]$，$E_o$ 为同一型商在归一奇函数上的下确界；下面的紧性计算证明二者由相应本征态达到。
若存在 $0<\delta<h$ 使
$$
 R_\delta:=
 \frac{\hbar^2\pi^2}{8m\delta^2}
 +\Lambda\delta^2(2h+\delta)^2
 <\Lambda h^4,
 \tag{3.7}
$$
则
$$
 0<E_e<E_o<V_b.
 \tag{3.8}
$$
例如取 $\delta=h/4$ 时，充分条件是
$$
 \frac{2\pi^2\hbar^2}{m\Lambda h^6}<\frac{175}{256}.
 \tag{3.9}
$$

**证明。**

**中间谱计算 3.4（[S] 闭型表示、紧嵌入与一维本征方程）。**

$\widehat H_q$ 有离散谱。其归一化基态可选为严格正的实偶函数
$\phi_e$，基态能量 $E_e>0$ 且为单重。
最低奇态可选为实函数 $\phi_o$，满足
$$
 \phi_o(q)>0\quad(q>0),\qquad \phi_o(0)=0,\qquad
 \phi_o'(0)>0.
 \tag{3.6}
$$
其能量 $E_o$ 满足 $E_o>E_e$。

谱计算：

由 $V(q)\to+\infty$，型范数有界的函数在 $|q|>R$ 的
$L^2$ 质量由 $(\inf_{|q|>R}V)^{-1}$ 一致控制并趋零；
在每个有界区间，$H^1$ 到 $L^2$ 的紧嵌入给出收敛子列。
合并内部紧性与外部尾界，得到型域到 $L^2$ 的紧嵌入，
故对应自伴算符有紧预解式，谱离散且极小值达到。

将基态极小化函数换为其绝对值不会增加导数型能量，
故可取非负基态。局部常微分方程正则性使它为 $C^2$。
若在某点为零，非负性使一阶导数也为零，
而二阶线性方程的初值唯一性使它恒为零，矛盾。
因此它严格正。
对同一能量的两个实本征函数，Wronskian 为常数；
本征函数及其导数都在 $L^2$，故该常数函数属于 $L^1(\mathbb R)$，
只能为零。因此它们线性相关，特别是基态单重。
空间反射保持算符、正性和归一化，唯一性使基态为偶函数。
若 $E_e=0$，二次型中的导数项为零，
函数必须为常数，不可能是非零的 $L^2(\mathbb R)$ 态，故 $E_e>0$。

在奇子空间中同样有达到的最低能级。
等价地在半轴上取 Dirichlet 条件 $u(0)=0$，
将最低函数选为非负；同一 ODE 唯一性使它在半轴内部严格正。
其奇延拓给出 $\phi_o$。右导数非负，
若为零，又由 $u(0)=u'(0)=0$ 强制零解，
故 $\phi_o'(0)>0$。
奇态与唯一偶基态正交，不可能具有相同的最低能量，
所以 $E_o>E_e$。

取型域中的归一化试探函数
$$
 u_\pm(q)=
 \begin{cases}
  \delta^{-1/2}\cos\!\dfrac{\pi(q\mp h)}{2\delta},
       &|q\mp h|\le\delta,\\
  0,&\text{其余}.
 \end{cases}
$$
这些连续分段光滑函数在 $H^1$ 中，
不要求它们在微分算符的算子域中。
积分给 $\left\lVert u_\pm\right\rVert=1$、
$\left\lVert u_\pm'\right\rVert^2=\pi^2/(4\delta^2)$。
在支撑上，
$|q^2-h^2|\le\delta(2h+\delta)$，故型能量至多为 $R_\delta$。
两支撑不交，内积和全部型交叉项为零。
因此 $(u_++u_-)/\sqrt2$ 为偶试探态，
$(u_+-u_-)/\sqrt2$ 为奇试探态，
两者的 Rayleigh 商均不大于 $R_\delta$。
分别在偶、奇子空间应用变分原理，得
$E_e,E_o\le R_\delta<V_b$。
能级严格排序由谱计算 3.4 给出。
代入 $\delta=h/4$ 后，势能上界为
$81\Lambda h^4/256$，即得式 (3.9)。

证毕。

### 3.3. 从两井到非零穿垒电流

**定理 3.6（完全在势垒下的跨井概率流）。**

采用定理 3.5 的条件，令
$$
 \Delta E=E_o-E_e>0,\quad
 |L\rangle=\frac{\phi_e-\phi_o}{\sqrt2},\quad
 |R\rangle=\frac{\phi_e+\phi_o}{\sqrt2},
$$
$$
 c=\int_0^\infty\phi_e(q)\phi_o(q)\,dq.
 \tag{3.10}
$$
则 $0<c<1/2$，且以下三条为精确公式：
$$
 \left|\langle R| e^{-it\widehat H_q/\hbar}|L\rangle\right|^2
     =\sin^2\frac{\Delta E\,t}{2\hbar},
 \tag{3.11}
$$
$$
 P_+(t):=\int_0^\infty
       |(e^{-it\widehat H_q/\hbar}L)(q)|^2\,dq
     =\frac12-c\cos\frac{\Delta E\,t}{\hbar},
 \tag{3.12}
$$
$$
 j(0,t)=
 \frac{\hbar}{2m}\phi_e(0)\phi_o'(0)
       \sin\frac{\Delta E\,t}{\hbar}
 =\frac{\Delta E\,c}{\hbar}
       \sin\frac{\Delta E\,t}{\hbar}.
 \tag{3.13}
$$
这条演化只含能量低于 $V_b$ 的两个本征态，
却有时刻在 $q=0$ 产生非零流。

**证明。**

偶奇性给二态正交归一，且各态的半轴范数平方均为 $1/2$。
半轴上的两函数严格正，因此 $c>0$；
Cauchy--Schwarz 给 $c\le1/2$。
若取等号，两函数在半轴成比例，由连续性延到零点，
与 $\phi_e(0)>0$、$\phi_o(0)=0$ 矛盾，所以严格小于 $1/2$。

演化显式为
$$
 \psi(q,t)=\frac{e^{-itE_e/\hbar}\phi_e(q)
                    -e^{-itE_o/\hbar}\phi_o(q)}{\sqrt2}.
$$
取与 $R$ 的内积得到
$\frac12(e^{-itE_e/\hbar}-e^{-itE_o/\hbar})$，
模平方为式 (3.11)。
展开 $|\psi|^2$ 并在半轴积分得到式 (3.12)。

一维 Schrödinger 流为
$j=(\hbar/m)\operatorname{Im}(\bar\psi\,\partial_q\psi)$。
在零点，$\phi_e'(0)=0$、$\phi_o(0)=0$，
代入上式便得式 (3.13) 的第一个表达式。
两本征方程相乘相减，并在半轴积分，给
$$
 \Delta E\,c
 =\frac{\hbar^2}{2m}\phi_e(0)\phi_o'(0).
 \tag{3.14}
$$
无穷端的 Wronskian 边界项为零：
其导数为常数倍 $\phi_e\phi_o\in L^1$，
故有极限；Wronskian 本身也在 $L^1$，
其极限只能是零。
式 (3.14) 给出第二个流表达式，
并验证 $P_+'(t)=j(0,t)$。
两个能量都低于 $V(0)$，且由连续性存在共同的中心禁阻邻域。
非零流通过该中心，故不是单纯重新命名两个本征态的结果。

证毕。

$L,R$ 是精确的正交二态组合，各自更偏向一个半轴；
本定理没有声称它们严格只支撑在各自井中。
当两井分离充分且基态对接近时，常用局域井近似才把它们近似当作左右局域态。
式 (3.11)--(3.14) 不依赖该近似。
时间 $t=\pi\hbar/\Delta E$ 时，$L$ 精确演化到一个共同相位乘以 $R$；
空间右侧概率从 $1/2-c$ 变成 $1/2+c$，不是一般地从零变成一。

**推论 3.7（位置分支不确定而相融关系稳定）。**

对归一化型域态 $\psi$，记能量期望
$\mathcal E=\mathfrak h[\psi]$。则
$$
 \left\langle(q^2-h^2)^2\right\rangle
 \le \frac{\mathcal E}{\Lambda},
 \qquad
 \Pr\{|q^2-h^2|\ge\varepsilon h^2\}
 \le\frac{\mathcal E}{\varepsilon^2V_b}\quad(\varepsilon>0).
 \tag{3.15}
$$
若 $\psi$ 的位置分布为偶函数，则 $\langle q\rangle=0$ 且
$$
 \left|\operatorname{Var}(q)-h^2\right|
 \le\sqrt{\frac{\mathcal E}{\Lambda}}.
 \tag{3.16}
$$
所以当 $\mathcal E/V_b$ 很小时，
三个正交残差以高概率很小，
而原点法向位置的方差仍接近 $h^2$。

**证明。**

动能项非负，故
$\Lambda\langle(q^2-h^2)^2\rangle\le\mathcal E$。
将非负随机变量 $(q^2-h^2)^2$ 与阈值
$\varepsilon^2h^4$ 比较即得概率界。
偶分布使均值为零；
Cauchy--Schwarz 给
$|\langle q^2-h^2\rangle|
\le\langle(q^2-h^2)^2\rangle^{1/2}$，得到式 (3.16)。

证毕。

这个推论精确实现了“自己在哪里不确定，但关系大致确定”。
对于定理 3.6 的演化，能量期望
$(E_e+E_o)/2$ 守恒，式 (3.15) 因而在全部时间都成立。
相融井之间的相干迁移不要求长期积累大的关系残差。

**命题 3.8（对角点的精确算符关系）。**

令 $\widehat q$ 为完整乘法域
$D(\widehat q)=\{\psi\in L^2:q\psi\in L^2\}$
上的自伴位置算符，定义仿射乘法算符
$$
 \widehat o=H+\widehat q\,n,\qquad
 \widehat d=p_1+p_3-H-\widehat q\,n.
$$
每个分量按其最大乘法域定义；作为向量乘法算符，两者的共同定义域为 $D(\widehat q)$。以下和式首先是在该共同域上的恒等式，其闭包是处处定义的有界常算符。方差、对称型协方差对任意归一化 $\psi\in D(\widehat q)$ 均成立；若要把协方差写为算符乘积期望，取 $\psi\in D(\widehat q^2)$，特别可取 $\psi\in\mathcal Q$：
$$
 \boxed{\widehat o+\widehat d=(p_1+p_3)I,}
 \tag{3.17}
$$
$$
 \operatorname{Var}(n\cdot\widehat o)=\operatorname{Var}(n\cdot\widehat d)=\operatorname{Var}(q),\qquad
 \operatorname{Cov}(n\cdot\widehat o,n\cdot\widehat d)=-\operatorname{Var}(q).
$$

**证明。**

两乘法算符在共同域相加时 $\widehat q$ 抵消，所得常乘法算符在稠密共同域上的限制闭包即为有界常算符。$\psi\in D(\widehat q)$ 保证 $\|q\psi\|^2$ 有限，足以定义方差和型协方差；$\mathcal Q\subset D(\widehat q^2)$ 还保证乘积有定义。
沿法向的两个中心化算符分别为 $\Delta q$ 和 $-\Delta q$，
故平方相同，乘积为 $-(\Delta q)^2$。

证毕。

因此某些关系可以作为算符恒等式严格成立，
而参与关系的两个点都没有确定位置。
这比把每个点分别赋予独立误差更贴近当前模型。

### 3.4. 尺度、作用量和不能越过的精确扇区

**定理 3.9（精确无量纲化与屏障作用量）。**

取 $x=q/h$，酉缩放 $(U\psi)(x)=\sqrt h\,\psi(hx)$，
并置
$$
 \epsilon_{\rm qm}=\frac{\hbar}{\sqrt{2m\Lambda}\,h^3}.
$$
则
$$
 U\widehat H_qU^{-1}
 =\Lambda h^4
 \left[-\epsilon_{\rm qm}^2\frac{d^2}{dx^2}+(x^2-1)^2\right].
 \tag{3.18}
$$
该指定一维势的零能量屏障作用量恰为
$$
 S_0=\int_{-h}^h\sqrt{2mV(q)}\,dq
 =\frac43\sqrt{2m\Lambda}\,h^3,\qquad
 \frac{S_0}{\hbar}=\frac{4}{3\epsilon_{\rm qm}}.
 \tag{3.19}
$$

**证明。**

变量替换使二阶导数带因子 $h^{-2}$，
而势能带因子 $h^4$，给出式 (3.18)。
在 $[-h,h]$ 中，
$\sqrt{V(q)}=\sqrt\Lambda(h^2-q^2)$；
积分为
$\sqrt{2m\Lambda}[h^2q-q^3/3]_{-h}^{h}$，即得式 (3.19)。

证毕。

$S_0$ 是精确积分，不是精确能级劈裂公式。
有限能量的半经典屏障积分须使用真实转向点和
$\int\sqrt{2m(V-E)}\,dq$；
把劈裂写成指数近似还需要半经典条件及前因子分析。
本模型的跨井流证明使用精确本征态，不依赖该近似。

**命题 3.10（相同四次势下的两半轴隔离边界）。**

在同一个 $L^2(\mathbb R)\simeq L^2(\mathbb R_+)\oplus L^2(\mathbb R_-)$ 上，若把四次势微分表达式改取两半轴在 $0$ 处 Dirichlet 的自伴直接和实现，则任意初态都没有跨半轴转移。所用块对角函数演算的中间结论如下。

若允许的 Hilbert 空间分成
$\mathcal H_+\oplus\mathcal H_-$，
且物理自伴 Hamilton 算符以直接和实现
$H=H_+\oplus H_-$，则
$$
 P_-e^{-itH/\hbar}P_+=0\qquad(t\in\mathbb R).
 \tag{3.20}
$$
有限维中，$[H,P_+]=0$ 即为足够条件。

**证明。**

自伴直接和的函数演算保持块对角，
故其酉演化也是两块的直接和。
两块之间的矩阵元恒为零。两半轴闭型域在零点有零迹，给出所述自伴直接和；它和定义 3.3 的全线型域具有不同的边界条件，故没有与定理 3.6 的非零流矛盾。

证毕。

本结论针对严格的动力学分离。
仅将配置集合写成两个离散点并不自动强制 Hamilton 算符块对角：
仍可另供 $|+\rangle\langle -|+|-\rangle\langle +|$ 这样的耦合，
但它是额外的动力学内容。
量子隧穿允许通过经典能量意义上的禁阻区，
不把已经被模型排除的逻辑矛盾状态自动加入允许空间。

## 4. 将观察者纳入量子系统：相对坐标中的隧穿

前一节的 $q$ 是三轴相容的法向配置自由度，其 $m$ 是另供的有效质量。
本节给出另一种标准物理实现：
把作为参照的观察者载体和目标都当作可运动量子系统。
它说明没有精确的外部原点不妨碍精确建立相对隧穿问题。
两粒子的质心与相对运动分解是标准结果 [F]；
量子参考系文献进一步讨论把参考系统本身作为量子物体时
状态、观测和动力学的变换 [Q]。
下面只使用一个平移不变两体模型，
其坐标变换不供应下述关系势或控制权限。

**定义 4.1（量子参照与关系势）。**

设参照载体 $O$ 的质量为 $M_O>0$，目标 $S$ 的质量为 $m_S>0$。
在 $L^2(\mathbb R^2)$ 中取标准位置和动量算符，
并选择只依赖相对位置的势 $V(X_S-X_O)$：
$$
 H_{\rm pair}=\frac{P_O^2}{2M_O}+\frac{P_S^2}{2m_S}
                   +V(X_S-X_O).
 \tag{4.1}
$$
假设选用的势使该表达式有声明的自伴实现；
本节随后使用的有限矩形势满足这一点。
势随参照载体移动，模型中没有另给固定于绝对坐标的外势。

**命题 4.2（含量子参照的关系矩形势垒）。**
在定义 4.1 的平移不变自伴实现中，相对质量为 $\mu=m_SM_O/(m_S+M_O)$。若相对势是以下宽度 $a$、高度 $V_0$ 的有限矩形势，则对每个 $0<E<V_0$，相对透射通量比为式 (4.5)。任意初始联合密度算子只通过其相对约化态影响相对演化；质心与相对部分相关也不改变这个结论。

**证明。**
采用 [F] 的质心—相对坐标分解与 [T] §2.4.2 的定态匹配；以下保留当前质量、宽度、能量和相关初态下所需的全部计算。

**两体分离的中间计算（4.2）。**

令
$$
 r=X_S-X_O,\qquad
 R=\frac{m_SX_S+M_OX_O}{M_O+m_S},
$$
$$
 P=P_S+P_O,\qquad
 p=\frac{M_OP_S-m_SP_O}{M_O+m_S},\qquad
 \mu=\frac{m_SM_O}{m_S+M_O}.
 \tag{4.2}
$$
这些对易关系在共同不变核 $\mathcal S(\mathbb R^2)$ 上解释：$[r,p]=[R,P]=i\hbar$，两个正则对子之间的交叉对易子为零。对有限矩形势，取 $H^2(\mathbb R^2)$ 上自由动能加有界乘法势的自伴实现；一般势须选择与以下张量和等价的自伴实现。于是
$$
 \boxed{
 H_{\rm pair}=
 \frac{P^2}{2(M_O+m_S)}+\frac{p^2}{2\mu}+V(r).
 }
 \tag{4.3}
$$
对于任意初始密度算符，包括质心与相对部分相关的状态，
相对约化态满足
$$
 \rho_{\rm rel}(t)=
 e^{-itH_{\rm rel}/\hbar}\rho_{\rm rel}(0)e^{itH_{\rm rel}/\hbar},
 \quad
 H_{\rm rel}=\frac{p^2}{2\mu}+V(r).
 \tag{4.4}
$$
因此保持初始相对约化态不变时，
仅改变质心的坐标不确定性不会改变相对隧穿规律。

计算：

坐标逆变换为
$$
 X_S=R+\frac{M_O}{M_O+m_S}r,\qquad
 X_O=R-\frac{m_S}{M_O+m_S}r.
$$
其 Jacobian 的绝对值为一，因而给出 $L^2$ 间的酉变量变换。
用标准正则对易关系展开即得所列对易子。
动量逆变换为
$$
 P_S=\frac{m_S}{M_O+m_S}P+p,\qquad
 P_O=\frac{M_O}{M_O+m_S}P-p.
$$
代入动能，两个 $Pp$ 交叉项抵消，
$p^2$ 的系数为
$\frac12(m_S^{-1}+M_O^{-1})=(2\mu)^{-1}$；
势能只含 $r$，得到式 (4.3)。

变换后的 Hilbert 空间为
$L^2(\mathbb R,dR)\otimes L^2(\mathbb R,dr)$，
两项作用在不同张量因子上，演化分解为
$U_{\rm cm}(t)\otimes U_{\rm rel}(t)$。
对第一因子取部分迹时，其内部酉共轭消去，
得到式 (4.4)。这个论证没有要求初态为乘积态。

上述结论不表示改变观察者制备永远没有影响。
改变 $O$ 的实际状态一般也会改变初始相对约化态；
改变相互作用、有效质量或相对势也会改变动力学。
定理精确分离的是共同位置不确定与真实关系自由度的变化。

**有限矩形匹配的中间计算（4.3）。**

在式 (4.4) 中取
$$
 V(r)=
 \begin{cases}
 V_0,&0<r<a,\\
 0,&r<0\ \text{或}\ r>a,
 \end{cases}
 \qquad V_0>0,\ a>0.
$$
对入射相对能量 $0<E<V_0$，置
$$
 k_E=\frac{\sqrt{2\mu E}}{\hbar},\qquad
 \varkappa_E=\frac{\sqrt{2\mu(V_0-E)}}{\hbar}.
$$
左右两外区具有相同波数，其透射通量比为
$$
 \boxed{
 T(E)=
 \left[
 1+\frac{V_0^2\sinh^2(\varkappa_Ea)}
          {4E(V_0-E)}
 \right]^{-1}>0.
 }
 \tag{4.5}
$$

计算：

定态散射方程在三段上的广义解写为
$$
 \psi_E(r)=
 \begin{cases}
 e^{ik_Er}+\mathfrak r\,e^{-ik_Er},&r<0,\\
 A\cosh(\varkappa_Er)+B\sinh(\varkappa_Er),&0<r<a,\\
 \mathfrak t\,e^{ik_Er},&r>a.
 \end{cases}
$$
势能有限，故在两边界匹配 $\psi_E$ 和 $\psi_E'$。
从右边界向左传播长度 $a$ 得
$$
 \psi_E(0)=\mathfrak t e^{ik_Ea}
 \left(\cosh(\varkappa_Ea)
       -i\frac{k_E}{\varkappa_E}\sinh(\varkappa_Ea)\right),
$$
$$
 \psi_E'(0)=\mathfrak t e^{ik_Ea}
 \left(-\varkappa_E\sinh(\varkappa_Ea)
       +ik_E\cosh(\varkappa_Ea)\right).
$$
左侧满足 $\psi_E(0)+\psi_E'(0)/(ik_E)=2$，所以
$$
 \mathfrak t=
 \frac{e^{-ik_Ea}}{
 \cosh(\varkappa_Ea)+
 i\dfrac{\varkappa_E^2-k_E^2}{2k_E\varkappa_E}
       \sinh(\varkappa_Ea)}.
$$
取模平方并用 $\cosh^2=1+\sinh^2$，
$$
 |\mathfrak t|^{-2}
 =1+\frac{(\varkappa_E^2+k_E^2)^2}
            {4k_E^2\varkappa_E^2}\sinh^2(\varkappa_Ea).
$$
再用
$\varkappa_E^2+k_E^2=2\mu V_0/\hbar^2$ 得式 (4.5)。
两外区的概率流系数相同，因此
$T=|\mathfrak t|^2$。
分母有限且正，故 $T>0$。

这是广义定态散射解的通量计算，不把不可归一化平面波称为归一化局域态。
有限矩形势垒的标准匹配推导见 Tong 第 2.4.2 节 [T]；
本节的关系坐标与约化质量由命题 4.2 指定。
在 $\varkappa_Ea\to\infty$ 时，
$$
 T(E)\sim
 \frac{16E(V_0-E)}{V_0^2}e^{-2\varkappa_Ea}.
 \tag{4.6}
$$
式 (4.6) 直接来自精确公式的双曲正弦渐近，
不是把位置认识误差代入一个概率猜测。势垒端点的点值不影响乘法算符；$E=0$ 不是上述非零入射通量的定义域，$E=V_0$ 也不代入含 $1/\varkappa_E$ 的中间式。固定 $V_0,a,\mu$ 时，$E\downarrow0$ 的极限为零，而 $E\uparrow V_0$ 时由 $\sinh x/x\to1$ 得 $T\to[1+\mu V_0a^2/(2\hbar^2)]^{-1}$；固定 $0<E<V_0$ 时 $a\downarrow0$ 给 $T\to1$。

证毕。

## 5. 五模式中的失谐桥接、相消与长时间可达性

本节给出一个可精确求解的动力学扩充，以检验“关系大致相同，
却可能具有突兀的远期差异”这一判断。
沿用五模式标签与潜在耦合边
$01,02,03,1\!-\!13,3\!-\!13$，
但另行加入内部失谐、边相位和耦合标定。
这些控制不是既有固定生成元及等待读出菜单自动提供的能力
 [B],[H]。
因此下文是指定 Hamiltonian 下的条件定理，
不声称原生观察协议已经实现了这些额外控制。
固定 $\hbar>0$；$\Delta,J,g$ 均为能量量纲，
时间演化统一为 $U_t=e^{-itH/\hbar}$。

### 5.1. 精确静态消元与递归记忆

**定义 5.1（边界与内部划分）。**

令边界为 $L=0,R=13$，内部为 $a=1,b=3,c=2$。
按边界、内部的块次序，写
$$
H=\begin{pmatrix}A&B\\B^\dagger&D\end{pmatrix},
\qquad
A=\operatorname{diag}(\epsilon_L,\epsilon_R),\qquad
D=\operatorname{diag}(\Delta_a,\Delta_b,\Delta_c),
$$
$$
B=\begin{pmatrix}
t_a&t_b&g\\
\overline{s_a}&\overline{s_b}&0
\end{pmatrix}.
$$
对角能量为实数，耦合允许为复数；例如
$H_{L,a}=t_a,H_{a,R}=s_a$。
记边界正交投影为 $P$，内部投影为 $Q=I-P$。
以后把 $PU_tP$ 按边界空间 $\mathbb C^2$ 上的算子理解。

**定理 5.2（两桥一叶图的 Schur 响应及内部幅度界）。**

对 $E\in\mathbb C\setminus\{\Delta_a,\Delta_b,\Delta_c\}$，定义
$$
H_{\mathrm{eff}}(E)=A+B(EI-D)^{-1}B^\dagger.
$$
完整本征方程 $H(x,y)=E(x,y)$ 等价于
$$
H_{\mathrm{eff}}(E)x=Ex,\qquad
y=(EI-D)^{-1}B^\dagger x.
$$
非零本征向量必有 $x\ne0$。边界有效耦合为
$$
\boxed{
\bigl(H_{\mathrm{eff}}(E)\bigr)_{LR}
=\frac{t_as_a}{E-\Delta_a}
 +\frac{t_bs_b}{E-\Delta_b}.}
$$
两个对角修正分别为
$$
\Sigma_L(E)=
\frac{|t_a|^2}{E-\Delta_a}
+\frac{|t_b|^2}{E-\Delta_b}
+\frac{|g|^2}{E-\Delta_c},
\qquad
\Sigma_R(E)=
\frac{|s_a|^2}{E-\Delta_a}
+\frac{|s_b|^2}{E-\Delta_b}.
$$
若 $\eta=\min_j|E-\Delta_j|>0$，则
$$
\left\lVert y\right\rVert\le \frac{\left\lVert B\right\rVert_{\mathrm{op}}}{\eta}\left\lVert x\right\rVert.
$$
对归一化本征向量，因而有
$$
\left\lVert y\right\rVert^2\le
\frac{\left\lVert B\right\rVert_{\mathrm{op}}^2}
{\eta^2+\left\lVert B\right\rVert_{\mathrm{op}}^2}.
$$

**证明。**

采用 [H] §52.4 的有限块消元，取其 $H_{BB}=A,H_{BI}=B,H_{II}=D$。内部行是 $(EI-D)y=B^\dagger x$；
在声明的逆域内解出 $y$，代入边界行即得等价关系和各矩阵元。
若 $x=0$，可逆性强制 $y=0$。
$D$ 对角，故 $\left\lVert (EI-D)^{-1}\right\rVert_{\mathrm{op}}=1/\eta$，
得到范数界。归一化时
$\left\lVert y\right\rVert^2\le(\left\lVert B\right\rVert_{\mathrm{op}}/\eta)^2(1-\left\lVert y\right\rVert^2)$，
移项即得最后一式。

证毕。

在本模型的完整谱应用中，Schur 响应与全态范数还采用 [H] §52.4 的参数对应
$$
S(z)=A-zI_2-B(D-zI_3)^{-1}B^\dagger
=H_{\mathrm{eff}}(z)-zI_2.
$$
对实数 $E\notin\operatorname{spec}D$、$S(E)x=0$，重建 $\psi=(x,y)$ 后有
$$
\|\psi\|^2=-x^\dagger S'(E)x,\qquad
S'(E)=-I_2-B(D-EI)^{-2}B^\dagger.
$$
证明是将 $y=-(D-EI)^{-1}B^\dagger x$ 代入 $\|x\|^2+\|y\|^2$ 并微分逆矩阵。边界分量单位化一般不等于全态单位化。对任意复数非极点 $z$，正确范数式是
$$
\|(x,-(D-zI)^{-1}B^\dagger x)\|^2
=x^\dagger\bigl[I_2+B(D-\overline z I)^{-1}(D-zI)^{-1}B^\dagger\bigr]x;
$$
不能用 $-S'(z)$ 替代其中的伴随预解式乘积；自伴 $H$ 的真实本征能量仍是实数。

在内部本征值 $E$ 上，令 $K=D-EI$、$\Pi_E$ 为 $\ker K$ 的正交投影、$K^+$ 为 $K$ 在核正交补上的逆而在核上为零。全部极点本征向量精确满足
$$
\Pi_E B^\dagger x=0,\quad
y=-K^+B^\dagger x+u,\quad u\in\ker K,\quad
(A-EI-BK^+B^\dagger)x+Bu=0.
$$
内部方程 $Ky=-B^\dagger x$ 的可解条件就是第一式，按核分解得到第二式，再代回边界行即得第三式；因两内部部分正交，范数为 $\|x\|^2+\|K^+B^\dagger x\|^2+\|u\|^2$。特别地 $x=0,u\in\ker K\cap\ker B$ 给暗态，但极点态不必全为暗态。非极点的行列式分解
$$
\det(H-zI_5)=\det(D-zI_3)\det S(z)
$$
由块三角消元得到；右端约去分母后作为多项式恒等式延到极点，不能删去其零点重数。共同失谐族的五个本征值还将在下面直接列出。

叶子 $F[2]$ 在此精确消元中增加 $L$ 的自能，
却没有增加第三条直接的 $L$--$R$ 桥项。
它仍能通过改变共振条件影响迁移。
在 $E=\Delta_j$ 处不能使用逆式，相关暗态必须回到完整矩阵检查。

**定理 5.3（消去内部变量产生精确记忆核）。**

设 $i\hbar\dot\psi=H\psi$，写 $\psi=(x,y)$。
对 $t\ge0$，内部消元给
$$
\begin{aligned}
i\hbar\dot x(t)
={}&Ax(t)+Be^{-itD/\hbar}y(0)\\
&-\frac{i}{\hbar}\int_0^t
Be^{-i(t-s)D/\hbar}B^\dagger x(s)\,ds.
\end{aligned}
$$
当 $A=0,D=\Delta I$，记 $M=BB^\dagger$，则核为
$e^{-i\Delta(t-s)/\hbar}M$，并有等价的二阶边界方程
$$
\hbar^2\ddot x+i\hbar\Delta\dot x+Mx=0,
\qquad i\hbar\dot x(0)=By(0).
$$

**证明。**

内部方程的变常数解为
$$
y(t)=e^{-itD/\hbar}y(0)
-\frac{i}{\hbar}\int_0^t
e^{-i(t-s)D/\hbar}B^\dagger x(s)\,ds.
$$
代入 $i\hbar\dot x=Ax+By$ 即得。
在指定共同失谐情形，对边界方程再求导，
并用 $i\hbar\dot y=B^\dagger x+\Delta y$，
得到 $-\hbar^2\ddot x=Mx+i\hbar\Delta\dot x$。

证毕。

若 $B\ne0$，不同内部初态可以具有相同 $x(0)$，
却有不同 $By(0)$，从而给不同 $\dot x(0)$。
所以对全部自由初态，当前边界幅度一般不能单独决定下一步。
递归消元没有自动产生瞬时封闭的 Markov 更新；
隐藏初值或记忆核必须保留。

### 5.2. 共同失谐的精确五模式模型

**定义 5.4（失谐桥接族）。**

取 $J>0,g\ge0,\Delta>0,\phi\in\mathbb R$。
按原模式次序 $(0,1,2,3,13)$ 定义
$$
H_{\Delta,\phi,g}=
\begin{pmatrix}
0&J&g&J&0\\
J&\Delta&0&0&J\\
g&0&\Delta&0&0\\
J&0&0&\Delta&Je^{i\phi}\\
0&J&0&Je^{-i\phi}&0
\end{pmatrix}.
$$
在定义 5.1 的块次序中，
$$
A=0,\qquad D=\Delta I_3,\qquad
B=\begin{pmatrix}J&J&g\\J&Je^{-i\phi}&0\end{pmatrix}.
$$
定义
$$
c_\phi=J^2(1+e^{i\phi}),\qquad
S=4J^2+g^2,\qquad
d_*=\sqrt{g^4+4|c_\phi|^2},
$$
$$
M=BB^\dagger=
\begin{pmatrix}2J^2+g^2&c_\phi\\
\overline{c_\phi}&2J^2\end{pmatrix},
\qquad
\mu_\pm=\frac{S\pm d_*}{2}.
$$
对 $\mu\ge0$，置
$$
\Omega_\mu=\sqrt{\Delta^2+4\mu},\qquad
\lambda_{\mathrm{low}}(\mu)=\frac{\Delta-\Omega_\mu}{2},\qquad
\lambda_{\mathrm{high}}(\mu)=\frac{\Delta+\Omega_\mu}{2},
$$
$$
f_t(\mu)=
e^{-i\Delta t/(2\hbar)}
\left(
\cos\frac{\Omega_\mu t}{2\hbar}
+i\frac{\Delta}{\Omega_\mu}
\sin\frac{\Omega_\mu t}{2\hbar}
\right).
$$

**定理 5.5（精确谱与边界传播）。**

模型 5.4 的边界传播为
$$
\boxed{PU_tP=f_t(M).}
$$
按重数记，全体五个本征值为
$$
\lambda_{\mathrm{low}}(\mu_+),\
\lambda_{\mathrm{high}}(\mu_+),\
\lambda_{\mathrm{low}}(\mu_-),\
\lambda_{\mathrm{high}}(\mu_-),\
\Delta.
$$
当 $\mu_-=0$ 时，该通道贡献 $0,\Delta$；
因此上述列表也覆盖秩退化的情形。因 $J>0$，$B$ 至少秩一，且 $\mu_-=0$ 恰在 $g=0,\phi=0\pmod{2\pi}$，此时 $\Delta$ 在完整谱中有重数二；$d_*=0$ 恰在 $g=0,\phi=\pi\pmod{2\pi}$，此时两奇异值相等，两个低支、两个高支分别按重数保留。

**证明。**

对 $B$ 作奇异值分解。
$M$ 的单位本征向量 $u$ 若对应 $\mu>0$，
则 $B^\dagger u/\sqrt\mu$ 为单位内部向量。
这两个向量张成的不变子空间上，$H$ 的矩阵为
$$
\begin{pmatrix}0&\sqrt\mu\\\sqrt\mu&\Delta\end{pmatrix}.
$$
其特征方程为 $\lambda^2-\Delta\lambda-\mu=0$。
减去 $\Delta I/2$ 后的矩阵平方为 $\Omega_\mu^2 I/4$，
故指数的边界对角元正是 $f_t(\mu)$，
内部转移元为
$$
-i e^{-i\Delta t/(2\hbar)}
\frac{2\sqrt\mu}{\Omega_\mu}
\sin\frac{\Omega_\mu t}{2\hbar}.
$$
第三个内部方向不与边界耦合，本征值为 $\Delta$。
零奇异值通道按零耦合块处理，或由连续性取极限。
各奇异通道正交，遂得到矩阵函数公式和完整谱。再由 $\det M=4J^4\sin^2(\phi/2)+2J^2g^2$ 与 $d_*^2=g^4+4|c_\phi|^2$ 得所述退化条件；这些计算从完整块矩阵保留了内部极点 $\Delta$。

证毕。

**推论 5.6（所有时间上的小内部占据）。**

对任意归一边界初态 $\psi=P\psi$，
$$
\boxed{
\left\lVert QU_t\psi\right\rVert^2
\le\frac{4\mu_+}{\Delta^2+4\mu_+}
\le\frac{4\mu_+}{\Delta^2}
\quad(t\in\mathbb R).}
$$

**证明。**

在每个奇异通道中，内部概率为该通道初始权重乘
$4\mu\sin^2(\Omega_\mu t/(2\hbar))/(\Delta^2+4\mu)$。
对正交通道相加，再用 $\mu\mapsto4\mu/(\Delta^2+4\mu)$ 单调递增即可。

证毕。

### 5.3. 精确低支动力学与受控二阶近似

**定理 5.7（低支近似的统一误差）。**

在边界空间上定义
$$
H_{\mathrm{low}}
=\frac{\Delta I_2-\sqrt{\Delta^2 I_2+4M}}2.
$$
则对所有 $t$，
$$
\boxed{
\left\lVert PU_tP-e^{-itH_{\mathrm{low}}/\hbar}\right\rVert_{\mathrm{op}}
\le\frac{2\mu_+}{\Delta^2}.}
$$
并且
$$
\left\lVert H_{\mathrm{low}}+M/\Delta\right\rVert_{\mathrm{op}}
\le\frac{\mu_+^2}{\Delta^3},
$$
$$
\boxed{
\left\lVert PU_tP-e^{itM/(\hbar\Delta)}\right\rVert_{\mathrm{op}}
\le\frac{2\mu_+}{\Delta^2}
+\frac{|t|\mu_+^2}{\hbar\Delta^3}.}
$$

**证明。**

令
$$
b_\mu=\frac{1-\Delta/\Omega_\mu}{2},\qquad a_\mu=1-b_\mu.
$$
二阶谱分解给
$$
f_t(\mu)=
a_\mu e^{-it\lambda_{\mathrm{low}}(\mu)/\hbar}
+b_\mu e^{-it\lambda_{\mathrm{high}}(\mu)/\hbar}.
$$
因此
$$
\left|f_t(\mu)-e^{-it\lambda_{\mathrm{low}}(\mu)/\hbar}\right|
\le2b_\mu\le\frac{2\mu}{\Delta^2}.
$$
最后一个不等式可由
$b_\mu=2\mu/[\Omega_\mu(\Omega_\mu+\Delta)]$
直接得到。谱函数演算给第一项算子界。

有理化给精确恒等式
$$
0\le\lambda_{\mathrm{low}}(\mu)+\frac\mu\Delta
=\frac{4\mu^2}{\Delta(\Delta+\Omega_\mu)^2}
\le\frac{\mu^2}{\Delta^3}.
$$
再用谱函数演算得到 Hamiltonian 界。
两个有限维自伴生成元的 Duhamel 估计为
$$
\left\lVert e^{-itA/\hbar}-e^{-itA'/\hbar}\right\rVert_{\mathrm{op}}
\le\frac{|t|}{\hbar}\left\lVert A-A'\right\rVert_{\mathrm{op}}.
$$
它来自对
$e^{-i(t-s)A/\hbar}e^{-isA'/\hbar}$
求导后积分；指数因子酉性使积分范数受所示常数控制。
应用该式并用三角不等式，得到最后一项。

证毕。

第一项是使用精确低支本征值的全时间误差界；
第二阶有效生成元 $-M/\Delta$ 的误差则含时间因子。
临近完全相消时，所需迁移时间可能发散，
不能把固定时间的二阶近似当作对全部长时间统一有效。
以下的迁移结论使用精确本征值。

**定理 5.8（迁移幅度、叶子失谐及精确低支时刻）。**

若 $d_*>0$，则
$$
\boxed{
A_{RL}(t):=\langle R| U_t|L\rangle
=\frac{\overline{c_\phi}}{d_*}
\bigl(f_t(\mu_+)-f_t(\mu_-)\bigr).}
$$
从而
$$
\boxed{
|A_{RL}(t)|^2\le
\frac{4|c_\phi|^2}{g^4+4|c_\phi|^2}.}
$$
若 $c_\phi\ne0$，令
$$
\delta\lambda
=\lambda_{\mathrm{low}}(\mu_-)-\lambda_{\mathrm{low}}(\mu_+)>0,
\qquad
t_*=\frac{\pi\hbar}{\delta\lambda}.
$$
则
$$
|A_{RL}(t_*)|
\ge\frac{|c_\phi|\Delta}{d_*}
\left(\frac1{\Omega_{\mu_+}}+\frac1{\Omega_{\mu_-}}\right).
$$
特别，当 $1-S/\Delta^2>0$ 时，
$$
|A_{RL}(t_*)|
\ge\frac{2|c_\phi|}{d_*}
\left(1-\frac S{\Delta^2}\right).
$$
若 $d_*=0$，则 $M$ 为标量矩阵，迁移幅度恒为零。

**证明。**

$M$ 的两个谱投影，其 $(R,L)$ 矩阵元分别为
$\overline{c_\phi}/d_*$ 与 $-\overline{c_\phi}/d_*$，
故传播公式成立。
每个 $f_t(\mu)$ 是一个酉二阶块的矩阵元，绝对值至多一，
得到幅度上界。

在 $t_*$，两个低支相位相差 $\pi$。
用定理 5.7 证明中的 $a_\mu,b_\mu$ 分解，
低支差的绝对值是 $2-b_{\mu_+}-b_{\mu_-}$，
高支差的绝对值至多 $b_{\mu_+}+b_{\mu_-}$。
反三角不等式因此给
$$
|A_{RL}(t_*)|
\ge\frac{2|c_\phi|}{d_*}
(1-b_{\mu_+}-b_{\mu_-}).
$$
代入 $b_\mu$ 得第一下界；
再用 $b_{\mu_+}+b_{\mu_-}\le(\mu_++\mu_-)/\Delta^2=S/\Delta^2$
得到简化下界。退化情形由矩阵函数直接判断。

证毕。

在 $\phi=0$ 时，上界为
$16J^4/(g^4+16J^4)$。
所以这个对称族中固定非零、未补偿的叶子耦合限制了迁移幅度；
它改变的是相对自能。该结论不排除另行调节边界能量后的其他共振模型。

### 5.4. 任意小内部占据下的精确完美迁移

**定理 5.9（失谐方形的精确序列）。**

在 $g=0,\phi=0$ 的子族中，第五个模式是明确解耦的旁观者。
对初态 $|L\rangle$，令 $\Omega=\sqrt{\Delta^2+16J^2}$。
则
$$
A_{RL}(t)=\frac{f_t(4J^2)-1}{2},
\qquad
p_Q(t):=\left\lVert QU_t|L\rangle\right\rVert^2
=\frac{8J^2}{\Delta^2+16J^2}
\sin^2\frac{\Omega t}{2\hbar}.
$$
对每个整数 $n\ge1$，取
$$
\boxed{
\Delta_n=\frac{4Jn}{\sqrt{2n+1}},
\qquad
T_n=\frac{\pi\hbar\sqrt{2n+1}}{2J}.}
$$
则
$$
\boxed{U_{T_n}|L\rangle=-|R\rangle,}
\qquad
\boxed{\sup_t p_Q(t)=\frac{2n+1}{2(n+1)^2}\longrightarrow0.}
$$

**证明。**

此时 $\mu_+=4J^2,\mu_-=0$。
边界亮态 $(|L\rangle+|R\rangle)/\sqrt2$ 与内部
$(|1\rangle+|3\rangle)/\sqrt2$ 的耦合为 $2J$；
边界暗态 $(|L\rangle-|R\rangle)/\sqrt2$ 的能量为零。
初态在亮通道的权重为 $1/2$，所以定理 5.5
给出幅度和内部占据公式。

对所选参数，
$$
\Omega_n=\frac{4J(n+1)}{\sqrt{2n+1}},
\qquad
\frac{\Omega_nT_n}{2\hbar}=(n+1)\pi,\qquad
\frac{\Delta_nT_n}{2\hbar}=n\pi.
$$
因此内部转移振幅为零，亮态回返振幅
$e^{-in\pi}\cos((n+1)\pi)=-1$。
暗态不变，故完整输出为 $-|R\rangle$。
对内部占据取正弦平方的最大值，再代入 $\Omega_n$，
得到精确上确界。

证毕。

这给出一条严格的隧穿型结论：
高失谐内部模式的占据可以在所有时刻都任意小，
边界仍能发生完整相干迁移，而迁移时间随势垒参数增长。
沿上述序列，
$T_n\sim\pi\hbar\Delta_n/(4J^2)$。
时间无关的 $H$ 保持总能量；局域初态并非能量本征态，
无需采用“临时借能量”的解释。
若要把这称为实际位置空间中的势垒隧穿，
还须供应位置嵌入、动能、势能和能量制备的对应。

### 5.5. 完全相消、有限时间稳定与无限时间突变

**定理 5.10（暗相位上的全时间隔离）。**

在 $\phi=\pi\pmod{2\pi}$ 时，对任意 $g\ge0$，
$$
\boxed{A_{RL}(t)=0\quad(t\in\mathbb R).}
$$
若两臂耦合仍为相反相位但内部能量变为
$\Delta_a,\Delta_b$，则逆域内的有效耦合为
$$
J_{LR}(E)
=\frac{J^2(\Delta_a-\Delta_b)}
{(E-\Delta_a)(E-\Delta_b)}.
$$

**证明。**

等失谐情形 $c_\phi=0$，$M$ 对角，故 $f_t(M)$ 无交叉矩阵元。
也可在内部改用
$|\pm\rangle=(|1\rangle\pm|3\rangle)/\sqrt2$：
$\operatorname{span}\{|L\rangle,|+\rangle,|2\rangle\}$ 与
$\operatorname{span}\{|R\rangle,|-\rangle\}$ 为正交不变子空间。
异失谐式由定理 5.2 中
$J^2/(E-\Delta_a)-J^2/(E-\Delta_b)$ 通分得到。

证毕。

这里有两条几何路径，传输为零来自相干相消。
边的模长和点间连接未固定该回路相位。
顶点相位变换同时改变两条路径的端点相位因子，
其乘积比保持不变，故相对路径相位并非任意坐标原点的共同平移。

**定理 5.11（共振子族的非一致长时间极限）。**

固定 $g=0$ 与 $\Delta>2J$，并取 $0\le T<\infty$。定义
$$
\mathcal P_T(\phi)=\sup_{0\le t\le T}|A_{RL}^{\phi}(t)|^2,
\qquad
\mathcal P_\infty(\phi)=\sup_{t\ge0}|A_{RL}^{\phi}(t)|^2.
$$
则
$$
\mathcal P_\infty(\pi)=0,
$$
而每个 $\phi\ne\pi\pmod{2\pi}$ 都满足
$$
\boxed{
\mathcal P_\infty(\phi)\ge
\left(1-\frac{4J^2}{\Delta^2}\right)^2>0.}
$$
使用定理 5.8 的精确 $t_*(\phi)$，
当 $\phi\to\pi$ 且 $\phi\ne\pi$ 时，
$$
\boxed{
t_*(\phi)\sim
\frac{\pi\hbar\sqrt{\Delta^2+8J^2}}
{2J^2|\phi-\pi|}.}
$$
但是每个固定有限 $T$ 都满足
$$
\boxed{
\mathcal P_T(\phi)
\le\frac{T^2J^2}{\hbar^2}|\phi-\pi|^2,
\qquad
\lim_{\phi\to\pi}\mathcal P_T(\phi)=0.}
$$

**证明。**

在非暗相位，$g=0$ 给
$d_*=2|c_\phi|$、
$\mu_\pm=2J^2\pm|c_\phi|$、
$S=4J^2$。
定理 5.8 的简化下界因此给无限时间下界。
暗相位结论由定理 5.10 给出。

当 $\phi\to\pi$，
$|c_\phi|=2J^2|\cos(\phi/2)|\sim J^2|\phi-\pi|$。
记 $\Omega_0=\sqrt{\Delta^2+8J^2}$。
对 $\lambda_{\mathrm{low}}(\mu)$ 求导得
$\lambda_{\mathrm{low}}'(\mu)=-1/\sqrt{\Delta^2+4\mu}$，
所以
$\delta\lambda\sim2|c_\phi|/\Omega_0$。
代入 $t_*=\pi\hbar/\delta\lambda$ 得时间渐近式。

最后，两矩阵只在一条边的相位上不同，
$$
\left\lVert H_\phi-H_\pi\right\rVert_{\mathrm{op}}
=J|e^{i\phi}+1|\le J|\phi-\pi|.
$$
定理 5.7 证明中的 Duhamel 估计，
结合暗相位的零矩阵元，给
$|A_{RL}^{\phi}(t)|\le |t|J|\phi-\pi|/\hbar$。
平方并在 $[0,T]$ 上取上确界即可。

证毕。

因而
$$
\liminf_{\substack{\phi\to\pi\\\phi\ne\pi}}
\mathcal P_\infty(\phi)>0
\quad\text{而}\quad
\mathcal P_\infty(\pi)=0.
$$
突变属于无限未来可达性的判据；
固定时间或固定预算下的状态与概率没有跳跃。
这明确展示了接近的局部读数与不同的远期关系性质可以共存。

**推论 5.12（固定非零叶子耦合抑制该无限时突变）。**

对同一对称 Hamiltonian 族，若固定 $g>0$，仍以该 $g$ 下的振幅定义 $\mathcal P_\infty(\phi)=\sup_{t\ge0}|A_{RL}^{\phi}(t)|^2$，
则即使取全部未来，
$$
\mathcal P_\infty(\phi)
\le
\frac{4|c_\phi|^2}{g^4+4|c_\phi|^2}
\le\frac{4J^4}{g^4}|\phi-\pi|^2
\longrightarrow0.
$$

**证明。**

第一项是定理 5.8 的全时间上界；
第二项使用 $|c_\phi|=J^2|1+e^{i\phi}|\le J^2|\phi-\pi|$。

证毕。

所以定理 5.11 的奇异极限依赖 $g=0$ 的共振子族，
不能泛化成所有五耦合参数的必然行为。
叶子带来的相对失谐可以使这个无限时间判据也恢复连续。
若观察者的不确定性只对应共同坐标平移，这些 Hamiltonian 参数都不变；
若它对应真实相对耦合、失谐或回路相位的不确定，
则必须具体进入本节的参数或联合量子状态，
才能得到相应迁移、相消或辨识结论。

## 6. 固定恢复任务中的分支切换与连续损失

固定通道下的单投影恢复损失可以写成到固定可达效果集的距离。以下在同一个通道与有限步数下比较目标效果；代数最优值取自 [M] 定理 35.1，距离估计与末端解码计算用于这一指定任务。

### 6.1. 固定三维任务与有限代数最优值

固定有序正交基 $(\xi,e,f)$，在 $M_3(\mathbb C)$ 上精确采用 [M] 定义 29.1 的矩阵与通道：
$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
$$
$$
\Delta_W(X)=\frac{X+WXW}{2},\qquad
\mathcal F(X)=U_0\Delta_W(X)U_0^\dagger
=\frac12U_0XU_0^\dagger+\frac12U_0WXWU_0^\dagger.
$$
这里 $W=W^\dagger=W^{-1}$、$U_0=U_0^\dagger=U_0^{-1}$；两 Kraus 算子 $U_0/\sqrt2,U_0W/\sqrt2$ 的伴随乘积和为 $I_3$，故 $\mathcal F$ 为 CPTP。每步独立公平选择这两个酉分支，抹除全部历史后恰为 $\mathcal F^n$；并且
$$
\mathcal F^\dagger(B)=\Delta_W(U_0^\dagger B U_0).
$$
对
$$
  0<p<1,\qquad n\geq 2,\qquad n\in\mathbb N,
$$
定义
$$
  v_p=\sqrt p\,\xi+\sqrt{1-p}\,e,
  \qquad E_p=|v_p\rangle\langle v_p|.
$$
输入域是全部 $\mathbb C^3$ 上的密度算子。恢复操作是一个在同一三维空间上作用、与未知输入无关的固定末端 CPTP 通道；它可以依赖于已知的 $p,n$ 以及指定模型，但不能访问已抹除的历史。这里没有额外参考系统、中间恢复、后选择或扩大输出空间。

按 [M] 定理 35.1，对上述每个 $p,n$，其第 31–34 节的有限代数根与筛选规则给出一个最优效果 $B_*$ 及精确值 $t$，满足
$$
  \eta_n(E_p)
  :=\min_{0\leq B\leq I_3}
       \left\lVert (\mathcal F^n)^\dagger(B)-E_p\right\rVert_{\mathrm{op}}
  =t.
  \tag{6.1}
$$
同空间的末端通道
$$
  \mathcal D_{B_*}(X)
  =\operatorname{Tr}(B_*X)E_p
   +\operatorname{Tr}((I_3-B_*)X)\frac{I_3-E_p}{2}
  \tag{6.2}
$$
达到相同的最坏情形任务误差：
$$
  \eta_n(E_p)
  =\min_{\mathcal D\ \mathrm{CPTP}}
    \sup_{\rho\in\mathcal S_3}
    \left|
       \operatorname{Tr}\bigl(E_p\mathcal D(\mathcal F^n(\rho))\bigr)
       -\operatorname{Tr}(E_p\rho)
    \right|,
  \tag{6.3}
$$
其中 $\mathcal S_3$ 为三维密度算子集。此处采用 [M] 定理 35.1 的精确最优值：其参数为 $q=1-p,c=\sqrt{pq},s=(-1/2)^{n-1}$，故有限步内 $s\ne0$；$n=2$ 与 $n=3$ 以及 $p=1/2$ 的分支均按该定理保留。它的根分类只在 $0<p<1,n\ge2$ 上调用，不取 $s=0$ 或人口端点极限。距离估计与投影解码等价不依赖这些根分类。 [M]

### 6.2. 固定效果像上的距离及其一致稳定性

**定义 6.1（固定通道的效果像与距离损失）。**

令 $d\geq2$ 有限，$\mathcal S_d=\{\rho=\rho^\dagger\ge0:\operatorname{Tr}\rho=1\}$，$\mathcal F:M_d(\mathbb C)\to M_d(\mathbb C)$ 为一个固定 CPTP 通道，$n\geq1$ 为固定整数。记
$$
  \mathsf{Eff}_d=\{B\in M_d(\mathbb C):B=B^\dagger,\ 0\leq B\leq I_d\},
  \qquad
  \mathcal C_n=(\mathcal F^n)^\dagger(\mathsf{Eff}_d).
$$
对任意效果 $A\in\mathsf{Eff}_d$，定义数值
$$
  \eta_n(A)
  :=\operatorname{dist}_{\mathrm{op}}(A,\mathcal C_n)
  =\min_{C\in\mathcal C_n}\left\lVert A-C\right\rVert_{\mathrm{op}}.
  \tag{6.4}
$$
这里的伴随按迹对偶定义，即
$\operatorname{Tr}(Y\mathcal F(X))=\operatorname{Tr}(\mathcal F^\dagger(Y)X)$。
对一般效果 $A$，式 (6.4) 首先是距离的定义；它本身不声称每个 $C\in\mathcal C_n$ 都能通过某个满足 $\mathcal D^\dagger(A)=B$ 的同空间末端解码实现。

由于 $\mathsf{Eff}_d$ 是有限维中的非空紧集，线性映射 $(\mathcal F^n)^\dagger$ 的像 $\mathcal C_n$ 也是非空紧集，故上述最小值确实达到。通道伴随正且保单位，因此 $\mathcal C_n\subseteq\mathsf{Eff}_d$。

**命题 6.2（固定 qutrit 任务的距离稳定与可实现末端解码）。**
对本节明确指定的 $\mathcal F$、任意有限 $n\ge2$ 与 $p,p'\in(0,1)$，式 (6.1) 的最优值满足式 (6.7) 的参数模量，对任意 $0<\delta<1/2$ 且 $p,p'\in[\delta,1-\delta]$ 还满足式 (6.8)。每个最优效果都可由同 qutrit、输入无关的固定 CPTP 末端通道实现，公式为式 (6.2)。

**证明。**
采用固定集合距离的三角不等式、Hermitian 期望的谱范数对偶与单投影测量—制备接口；后者在 [M] 定义 29.1、定理 35.1 中以同一合同使用。为使参数匹配和 CPTP 实现可直接核算，以下在其所需有限维范围内保留全部计算。

**中间计算 6.2（对目标效果的一致 $1$-Lipschitz 性）。**

在定义 6.1 的固定通道与固定步数下，对任意两个效果 $A,A'$ 有
$$
  \left|\eta_n(A)-\eta_n(A')\right|
  \leq\left\lVert A-A'\right\rVert_{\mathrm{op}}.
  \tag{6.5}
$$
这个常数不依赖于 $d,n$、效果最优解的唯一性，也不依赖于最优解用何种分支公式表示。

计算：

对每个 $C\in\mathcal C_n$，三角不等式给出
$$
  \left\lVert A-C\right\rVert_{\mathrm{op}}
  \leq\left\lVert A-A'\right\rVert_{\mathrm{op}}+\left\lVert A'-C\right\rVert_{\mathrm{op}}.
$$
对 $C$ 取下确界得到
$$
  \eta_n(A)\leq\left\lVert A-A'\right\rVert_{\mathrm{op}}+\eta_n(A').
$$
交换 $A,A'$ 即得式 (6.5)。这个论证事实上只需要 $\mathcal C_n$ 非空；紧性用于保证最小值达到，而不用于连续性估计。

**中间计算 6.3（项目 rank-one 任务之间的精确距离）。**

对上面的 $E_p,E_{p'}$，其中 $p,p'\in(0,1)$，有
$$
  \left\lVert E_p-E_{p'}\right\rVert_{\mathrm{op}}
  =\left|
       \sqrt{p(1-p')}-\sqrt{p'(1-p)}
    \right|.
  \tag{6.6}
$$

计算：

在 $\operatorname{span}\{\xi,e\}$ 上，令
$c=\sqrt{p(1-p)}$、$c'=\sqrt{p'(1-p')}$，则
$$
  E_p-E_{p'}
  =\begin{pmatrix}
      p-p'&c-c'\\
      c-c'&-(p-p')
    \end{pmatrix}.
$$
在其正交补上该算子为零。上述二阶 Hermitian 矩阵的两个特征值是
$$
  \pm\sqrt{(p-p')^2+(c-c')^2}.
$$
直接展开得
$$
\begin{aligned}
  (p-p')^2+(c-c')^2
  &=p+p'-2pp'-2\sqrt{pp'(1-p)(1-p')}\\
  &=\left(\sqrt{p(1-p')}-\sqrt{p'(1-p)}\right)^2.
\end{aligned}
$$
取最大特征值的绝对值即得结论。

**中间计算 6.4（任务参数的连续性与紧内区间估计）。**

固定同一个 $\mathcal F$ 及有限步 $n$，则
$$
  \left|\eta_n(E_p)-\eta_n(E_{p'})\right|
  \leq
  \left|\sqrt{p(1-p')}-\sqrt{p'(1-p)}\right|.
  \tag{6.7}
$$
尤其 $p\mapsto\eta_n(E_p)$ 在 $(0,1)$ 连续。进一步，对任意固定 $0<\delta<1/2$ 及 $p,p'\in[\delta,1-\delta]$，
$$
  \left|\eta_n(E_p)-\eta_n(E_{p'})\right|
  \leq\frac{|p-p'|}{2\sqrt{\delta(1-\delta)}}.
  \tag{6.8}
$$

计算：

式 (6.7) 是距离计算 6.2 与投影距离计算 6.3 的直接合成。令
$$
  \theta(p)=\arccos\sqrt p\in(0,\pi/2).
$$
于是 $\sqrt p=\cos\theta(p)$，$\sqrt{1-p}=\sin\theta(p)$，且
$$
  \left\lVert E_p-E_{p'}\right\rVert_{\mathrm{op}}
  =|\sin(\theta(p')-\theta(p))|
  \leq|\theta(p')-\theta(p)|.
$$
另一方面，
$$
  |\theta'(p)|=\frac1{2\sqrt{p(1-p)}}
  \leq\frac1{2\sqrt{\delta(1-\delta)}}
  \qquad(p\in[\delta,1-\delta]).
$$
由中值定理得到式 (6.8)。

这里统一的是不同目标任务之间的误差估计，而不是一个解码器同时对所有目标最优的断言。每个 $p$ 的最优末端通道仍可不同。

### 6.3. 非平凡投影任务与同空间解码的精确等价

**中间计算 6.5（任意有限维非平凡投影的单任务解码等价）。**

令 $d\geq2$，$\mathcal F$ 与 $n$ 如定义 6.1，并令
$$
  E=E^\dagger=E^2,\qquad r=\operatorname{rank}E,
  \qquad 1\leq r\leq d-1.
$$
则
$$
  \min_{0\leq B\leq I_d}
       \left\lVert (\mathcal F^n)^\dagger(B)-E\right\rVert_{\mathrm{op}}
  =\min_{\mathcal D\ \mathrm{CPTP}}
    \sup_{\rho\in\mathcal S_d}
      \left|
        \operatorname{Tr}\bigl(E\mathcal D(\mathcal F^n(\rho))\bigr)
        -\operatorname{Tr}(E\rho)
      \right|.
  \tag{6.9}
$$
右边的 $\mathcal D:M_d(\mathbb C)\to M_d(\mathbb C)$ 是固定、输入无关的同空间末端通道。对每个效果 $B$，通道
$$
  \mathcal D_B(X)
  =\operatorname{Tr}(BX)\frac Er
   +\operatorname{Tr}((I_d-B)X)\frac{I_d-E}{d-r}
  \tag{6.10}
$$
都满足
$$
  \mathcal D_B^\dagger(E)=B.
  \tag{6.11}
$$
因此左边任意最优效果都给出右边的一个实际最优解码器。退化投影 $E=0,I_d$ 不使用含 $1/r$ 或 $1/(d-r)$ 的制备式：二者任务误差恒为零，距离也分别以 $B=0,I_d$ 取零。

计算：

首先，对任意 Hermitian 算子 $H$，有
$$
  \sup_{\rho\in\mathcal S_d}|\operatorname{Tr}(H\rho)|
  =\left\lVert H\right\rVert_{\mathrm{op}}.
  \tag{6.12}
$$
因为在 $H$ 的谱分解中，$\operatorname{Tr}(H\rho)$ 是其特征值的一个凸组合，绝对值不超过最大特征值绝对值；取该极值特征值的单位特征向量所定义的纯态即达到此界。

任取右边一个 CPTP 通道 $\mathcal D$，令
$B_{\mathcal D}=\mathcal D^\dagger(E)$。由于 $\mathcal D^\dagger$ 正且保单位，
$$
  0\leq B_{\mathcal D}\leq I_d.
$$
由伴随定义及式 (6.12)，这个通道的最坏误差恰为
$$
\begin{aligned}
 &\sup_{\rho\in\mathcal S_d}
   \left|
     \operatorname{Tr}\bigl(E\mathcal D(\mathcal F^n(\rho))\bigr)-\operatorname{Tr}(E\rho)
   \right|\\
 &\hspace{2em}
   =\left\lVert (\mathcal F^n)^\dagger(B_{\mathcal D})-E\right\rVert_{\mathrm{op}}.
\end{aligned}
$$
因此所有解码器中可能达到的最小误差不小于左边的效果最小值。

反向取任意 $B\in\mathsf{Eff}_d$。下面直接验证式 (6.10) 为 CPTP，而不只使用它的形式。写
$$
  B=\sum_{j=1}^d b_j|u_j\rangle\langle u_j|,
  \qquad 0\leq b_j\leq1,
$$
其中 $(u_j)$ 为正交单位基。分别在 $\operatorname{ran}E$ 与 $\ker E$ 中选正交单位基 $(a_\alpha)_{\alpha=1}^r$、$(c_\beta)_{\beta=1}^{d-r}$，并置
$$
  K_{\alpha j}=\sqrt{\frac{b_j}{r}}\,
                  |a_\alpha\rangle\langle u_j|,
  \qquad
  L_{\beta j}=\sqrt{\frac{1-b_j}{d-r}}\,
                  |c_\beta\rangle\langle u_j|.
$$
则
$$
  \sum_{\alpha,j}K_{\alpha j}^\dagger K_{\alpha j}
  +\sum_{\beta,j}L_{\beta j}^\dagger L_{\beta j}
  =\sum_j\bigl(b_j+(1-b_j)\bigr)|u_j\rangle\langle u_j|
  =I_d.
$$
这些 Kraus 算子因此定义一个 CPTP 通道。直接相乘求和，所得恰为式 (6.10)。

又因 $E^2=E$、$E(I_d-E)=0$ 及 $\operatorname{Tr} E=r$，对任意 $X$ 有
$$
  \operatorname{Tr}\bigl(E\mathcal D_B(X)\bigr)
  =\operatorname{Tr}(BX)\frac{\operatorname{Tr}(E^2)}r
   +\operatorname{Tr}((I_d-B)X)\frac{\operatorname{Tr}(E(I_d-E))}{d-r}
  =\operatorname{Tr}(BX).
$$
迹配对非退化，故 $\mathcal D_B^\dagger(E)=B$。因此每个左边候选效果的误差都能由同空间解码器实际达到。左边在紧集 $\mathsf{Eff}_d$ 上取到最小值，代入一个最优 $B$ 即同时证明右边达到最小值及式 (6.9)。

这个证明使用了 $E$ 是非平凡投影；对一般效果 $A$，不能把式 (6.10) 中的 $E$ 直接替换为 $A$ 并沿用 $\mathcal D_B^\dagger(A)=B$。例如 $A=\lambda I_d$、$0<\lambda<1$ 时，每个保迹通道的伴随都满足 $\mathcal D^\dagger(A)=\lambda I_d$，因而根本不能实现任意效果 $B$。这个常效果反例只否定任意 $B$ 的解码可达性，不否定该常效果两种优化损失相等：$\mathcal F^\dagger(\lambda I)=\lambda I$ 使距离损失为零，而每个解码器对该目标的任务误差也为零。它也不是对所有可行目标的充要分类；例如任何同时具有本征值 $0,1$ 的效果，都可用对应单位本征向量 $a_1,a_0$ 的投影作两制备态：$\mathcal D_B(X)=\operatorname{Tr}(BX)|a_1\rangle\langle a_1|+\operatorname{Tr}((I-B)X)|a_0\rangle\langle a_0|$。上述 Kraus 计算去掉均分求和即证明此通道 CPTP；两制备态对该效果的期望为 $1,0$，所以其伴随也把该效果送到 $B$。此处的等价定理只使用已经证明的非平凡投影充分条件。距离定义与距离计算 6.2 对一般效果仍然有效。

证毕。

### 6.4. 分支变化的可检验含义

在项目的固定通道、有限步和单任务合同下，$E_p$ 是秩一投影，故投影解码计算 6.5 的条件成立；取 $d=3,r=1$，式 (6.10) 正是式 (6.2)。于是参数计算 6.4 同时约束效果优化值及实际同空间末端恢复的最小最坏误差。

因此，即使某个求解表示在相邻参数处选用了不同的代数根、证书家族或最优效果，仍有式 (6.7) 的同一个误差上界。这个结论不要求一个连续的最优解选择，也不要求目标损失处处可微。它严格排除了由证书分类切换直接推断最优任务损失跳跃的做法。

与观察者不确定性的联系由此获得了一个可计算层次：预测者可能改变自己使用的解释、控制或证书，而在同一实验任务下可比较的最优误差仍受到连续性约束。若要把某种关系突变解释为共振、隧穿或实际动力学跃迁，还必须另行指定相应的状态演化及可观测事件；本节的恢复定理只识别并证明了上述固定任务的稳定性。

## 7. 综合命题、可检验区别与待建立的物理对应

**定理 7.1（内生原点不确定性与关系隧穿的条件接合）。**

设以下条件成立：

1. 三个已标定、不共线的固定端点满足 $\alpha_i>0$，
       并采用定义 1.1 的正交与对角闭合律；
2. 两个镜像完成在实际状态空间中未被规范识别，
       且有一个实际关系读口能够区分它们的两侧；
3. 允许的软相融配置为 $o(q)=H+qn$，
       实际势能为 $\frac{k}{2}\sum_{i<j}g_{ij}(o(q))^2$；
4. 该相对自由度具有定义 3.3 的量子载体、
       有效质量、时间演化与位置概率读出；
5. 参数满足定理 3.5 的势垒下充分条件。

则两个精确相融完成具有相同的全部成对距离，
而该模型中存在仅含势垒下能级的状态演化，
使两侧关系概率发生变化，并在禁阻中心有非零概率流。
整个演化中，正交残差满足式 (3.15) 的能量界，
且原点与对角点始终满足精确算符闭合式 (3.17)。

**证明。**

原点分类与镜像距离结论来自
命题 2.2 与定理 2.3。
命题 2.5 给共同残差，定理 3.2 指定其法向屏障。
定理 3.5 提供两个低于屏障的能级，
定理 3.6 给出所需状态与严格的概率流。
推论 3.7 给关系残差界，
命题 3.8 给算符闭合式。

证毕。

这个综合命题是充分条件定理。
它不要求所有隧穿都来自两镜像原点，也不声称原点无法完全辨识就足够推出隧穿。
尤其，没有条件 3、4 时，同一静态相融集合可以配备完全静止的动力学；
没有条件 2 时，两井甚至不是两个可区分的物理事件。

**推论 7.2（点图与边的模长不能唯一决定传播）。**

取第 5 节的同一失谐图，固定 $J>0,\Delta>0,g>0$。
$\phi=0$ 与 $\phi=\pi$ 两个模型拥有完全相同的顶点、
非零边和全部边耦合模长，但前者有非零 $0\to13$ 转移，
后者的该转移对所有时间为零。

**证明。**

暗相位结论由定理 5.10 给出。
在 $\phi=0$ 时，$H_{RL}=0$ 且 $(H^2)_{RL}=2J^2$，
有限维矩阵指数的 Taylor 展开给
$$
 \langle R| e^{-itH/\hbar}|L\rangle
 =-\frac{J^2t^2}{\hbar^2}+O(t^3).
$$
因此在足够小而非零的时间上振幅非零。
两个模型只有一条边的相位不同，其模长和边支撑相同。

证毕。

这给“隐藏信息在关系或连线上”一个精确内容：
连通性和边模之外，还可存在影响整体传播的相对路径相位。
第 5 节又说明叶子 $F[2]$ 通过自能改变共振，
所以一个看似不在直接桥上的关系也可以约束远期转移。
相干线性波模型也可以实现其中部分干涉公式；
把其强度解释成量子事件概率仍须保留本模型已经声明的态与测量结构。

### 7.1. 五种现象的判定

**推论 7.2a（记录、几何与传播判据的区别）。** 在上文各自的条件下，有以下对应。证明分别是命题 1.3、定理 2.3、2.7、2.12、3.6、5.11、命题 6.2 与推论 5.12 的直接应用；表中不将一种现象作为另一种的充分条件。

| 现象 | 可计算条件 | 结论与适用范围 |
| --- | --- | --- |
| 共同原点不确定 | 全部对象共同平移或协变运输 | 关系记录和预测概率不变。 |
| 镜像完成不唯一 | $o_\pm$ 给相同十个距离 | 距离遗漏手性；是否为不同物理状态依赖规范商与额外读口。 |
| 反演或判定突变 | 面积趋零、$S_\varepsilon$ 阈值接通、证书家族切换 | 可发生在连续数据中，不推出状态跃迁或势垒穿透。 |
| 相干跨屏障迁移 | 有限关系势垒、非零耦合、允许的相干态和读口 | 双井低能流与失谐桥接分别可算；位置势垒与有限图需要各自实现映射。 |
| 无限时可达性突变 | $g=0$、$\phi\to\pi$、等待时间发散 | 固定预算概率连续；固定 $g>0$ 时叶子自能抑制这一突变。 |

### 7.2. 数学实现的共同对应条件

**假设 7.2b（共同标定与可用操作）。** 在同一个实际观察协议中同时给出以下量：
镜像分支的关系读口、正交残差的标定、罚函数是否为真实能量、
有效质量或有限图耦合、回路相位，以及共同时间尺度。
在这些共同条件下，各模型的条件结论为：

1. 对关系双井，三个残差在法向约束下应共同为 $q^2-h^2$；
       若横向自由度可动，需改用完整配置势和真实最低屏障，
       不能直接使用法向高度或作用量。
2. 在势垒下二态子空间中，
       时间频率为 $\Delta E/\hbar$，
       两侧概率与中心流满足式 (3.12)--(3.14)；
       能量守恒和关系残差界可以同时检验。
3. 对五模式图，扫描路径相位与内部失谐可检验暗桥、
       叶子自能和迁移幅度界；
       单纯比较五个占位概率无法完整标定这些相位。
4. 对同一个有限步恢复任务，
       参数变化造成的最优误差必须服从
       式 (6.7)；
       输出证书的分类切换不能替代操作误差的比较。

项目边界几何卷第 52.4 节已经提供适合继续接合的谱消元接口：
保留能量依赖 Schur 响应、内部谱例外和全态归一化。
在非例外能量 $z$ 上，其记号为
$$
 S(z)=H_{BB}-zI-H_{BI}(H_{II}-zI)^{-1}H_{IB},
$$
$$
 \det(H-zI)=\det(H_{II}-zI)\det S(z).
$$
当 $z$ 为实数非例外本征能量且 $S(z)b=0$ 时，全本征态范数平方为 $-b^\dagger S'(z)b$，一般不能只把边界分量归一化。复参数的重建范数使用第 5 节的伴随预解式乘积。
内部谱上的暗模式应由原块方程或完整多项式行列式保留，
而不能从消元表达式的一个分母就推断物理发散 [H]。
第 5 节的全五模式谱直接解决了这一例外问题。

**定义 7.3（实现映射的共同条件）。** 一份实现必须在同一来源上同时指定：配置到几何点的映射、记录 $\pi$、两支的物理区分、能量标定、允许的动能或边耦合、回路相位、时间单位及可调用读口。几何纤维不供应这些动力学数据；有限图的占据迁移与位置势垒隧穿的对应还要求保留实际配置域、能量与测量。


## 数学引文

[B]: https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md
[G]: https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md
[O]: https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md
[H]: https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md
[M]: https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY_II.md
[T]: https://www.damtp.cam.ac.uk/user/tong/qm/qmhtml/S2.html
[S]: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf
[F]: https://farside.ph.utexas.edu/teaching/qmech/Quantum/node59.html
[Q]: https://doi.org/10.1038/s41467-018-08155-0

- [B]：《AURIC FIB 关系丛与预测闭包理论》，定义 3.1、定理 3.2、定义 3.4、定理 7.3、命题 8.9–8.10：模式类型、完整函数代数、另供相干载体及控制菜单。
- [G]：《FIB-ATOM：观察者内生的三轴几何与预测接口》，定义 2.1、假设 2.2、定义 10.5 与推论 10.6：共同距离的 Gram 实现及标架／控制的区别。
- [O]：《观察者相对局部模型与未来可识别性》，§1–2，命题 1.6、2.4：候选域、记录与实际未来的类型。
- [H]：《FIB 原子递归全息边界几何》，§52.4，式 (52.14)–(52.18b)：能量依赖 Schur 消元、极点本征态与实能量全态归一化。
- [M]：《AURIC FIB 环境记录记忆第二卷》，定义 29.1、31.1 与定理 35.1：固定实际通道、全部复输入、有限步任务及代数最优值；单投影解码接口也见该卷引用的 Bény–Kempf–Kribs 可观测量纠错框架。
- [T]：David Tong, *Quantum Mechanics*, Chapter 2, §§2.3.3、2.3.4、2.4.2：一维谱、双井及有限矩形势垒的标准工具。
- [S]：Gerald Teschl, *Mathematical Methods in Quantum Mechanics: With Applications to Schrödinger Operators*, second edition, AMS, Graduate Studies in Mathematics 157, 2014，§2.3（定理 2.14）、§4.4 与第 9 章：闭型表示、变分原理和一维 Schrödinger 算符；此处四次势的紧预解式用型域紧嵌入证明。
- [F]：Richard Fitzpatrick, *Quantum Mechanics*, “Two-Particle Systems”，式 (437)–(449)：质心、相对坐标和约化质量，作为命题 4.2 的中间计算。
- [Q]：Flaminia Giacomini, Esteban Castro-Ruiz, Časlav Brukner, “Quantum mechanics and the covariance of physical laws in quantum reference frames”, *Nature Communications* **10**, 494 (2019), doi:10.1038/s41467-018-08155-0：量子参照的背景与协变条件。

## 追加锚（本行以下为增补区）

## 8. 稳定读出、隐藏相位与关系返回

### 8.1. 观察条件、来源类型与供应结构

本节沿用第 1 节的五模式次序，并把几何端点记为 $a_i$；$p_s$ 专指模式概率。以下 $Q=P_{13}$ 是联合模式投影，不是第 5 节的内部投影；以下 $J$ 是对角能量的混合差分，不是第 5 节的桥耦合常数。各自的载体和动力学按本节定义使用。

**约定 8.1（几何输入与观察稳定）。** 设几何模型另行给定实内积空间中的三个端点 $a_1,a_2,a_3$，并研究满足指定距离或正交条件的原点完成 $o$。例如，$(a_i-o)\cdot(a_j-o)=0$ 是一个明确的几何条件。端点在这一完成问题中固定，是模型的输入；它不推出模式 $F[1],F[2],F[3]$ 在所有动力学或本体解释中天然稳定。

对来源状态集 $\mathcal S$ 和指定观察映射 $\mathcal O:\mathcal S\to\mathcal Y$，定义当前观察等价与纤维为

$$
s\sim_{\mathcal O}s'\iff\mathcal O(s)=\mathcal O(s'),
\qquad
\mathcal F_y=\{s\in\mathcal S:\mathcal O(s)=y\}.
$$

沿一条状态轨迹，观察稳定指 $\mathcal O(s_t)$ 不变；不同状态也可落在同一纤维。此定义始终相对于给定来源、读口、标架、标定及记录范围。若观察者的标架发生改变，须将效果拉回共同标架后比较；在不同未知标架下数值相同不自动表示同一观察稳定。

**约定 8.2（概率与取得条件）。** 以下概率、期望与相关函数均为模型中的总体量。精确相等不是一份未知样本上同时取得全部精确参数的声明。用实验频率估计它们须另供制备、重复、测量及误差控制。公式描述相干演化的前提是中间没有未计入的退相干或破坏性仪器；若插入实际测量，须把它的状态更新和输出记录纳入模型。

**定义 8.3（五模式与三个占位效果）。** 固定

$$
\Sigma=(0,1,2,3,13),\qquad
\mathcal H=\mathbb C^5,
$$

并另供正交归一基 $(|s\rangle)_{s\in\Sigma}$。$0$ 表示空占位模式 $F[\mathrm{null}]$，$13$ 表示联合模式 $F[1,3]$；$|0\rangle$ 是单位向量，不是零向量。模式索引与几何端点是不同类型。采用下表的占位函数：

| 模式 $s$ | 输入子集 | 位串 $(x,z,y)$ | 代数坐标 $(x,y,z)$ |
| --- | --- | --- | --- |
| $0$ | $\varnothing$ | $000$ | $(0,0,0)$ |
| $1$ | $\{1\}$ | $100$ | $(1,0,0)$ |
| $2$ | $\{2\}$ | $010$ | $(0,0,1)$ |
| $3$ | $\{3\}$ | $001$ | $(0,1,0)$ |
| $13$ | $\{1,3\}$ | $101$ | $(1,1,0)$ |

这是关系丛卷 [B] 定义 3.1 的分量次序。在观察者相对卷 [O] 定义 4.1 中，同一输入模式记作 $s_0,s_1,s_2,s_3,s_{13}$，显示标签依次为 $\mathrm{null},[2],[3],[5],[2,5]$；标签 $[2,5]$ 不是数值乘积。[O] 使用 $(X,Z,Y)$ 排列三均值，本文使用 $(X,Y,Z)$，只交换后两行读出次序。

令

$$
P_s=|s\rangle\langle s|,\qquad
N_x=P_1+P_{13},\quad
N_y=P_3+P_{13},\quad N_z=P_2,\qquad Q=P_{13}.
$$

对密度矩阵 $\rho\ge0$、$\operatorname{Tr}\rho=1$，写

$$
p_s=\operatorname{Tr}(P_s\rho),\qquad
X=\operatorname{Tr}(N_x\rho)=p_1+p_{13},\quad
Y=\operatorname{Tr}(N_y\rho)=p_3+p_{13},\quad Z=p_2.
$$

这些投影满足

$$
[N_i,N_j]=0,\qquad
N_xN_y=Q\ne0,\qquad N_xN_z=N_yN_z=0.
$$

因此几何腿向量正交、模式基向量正交、占位效果可交换，是三个不同陈述。尤其 $N_x,N_y$ 虽可交换，却不是互斥的正交投影；它们的共同占位正是模式 $13$。由模式名称或五个标签，不能推出几何空间、此五维 Hilbert 空间和另一个量子位空间相互同一，也不能推出一个张量分解。

这里消费的既有中间结果是：[B] 定理 3.2–3.3 的五点函数展开和概率纤维、定理 4.2 的复关系坐标、命题 8.9–8.10 与 10.3 的有条件控制接口、定理 7.3 与 8.4 的下降和输出解析闭包；[O] §4 的读口范围；[L] 定义 9.1 的局部 Bloch 接口及其取得限制；[C] 的逐输出闭包与平均通道之区别。[B79] 定理 8.4、命题 8.9–8.10、10.3 及 §18.1–18.2 已分别提供闭包、合法控制与关系相位的接口；本文对指定五模式准备和端点脉冲作具体应用，不以这些应用重新建立一套一般闭包或层析理论。以下各处列出参数对应及普通证明。

### 8.2. 两种稳定三读口的完整概率纤维

**命题 8.4（固定三个单模式概率）。** 令给定的三个实数为

$$
p_1=a,\qquad p_2=b,\qquad p_3=c.
$$

在概率单纯形 $\Delta^4=\{p_s\ge0:\sum_sp_s=1\}$ 中，相容纤维非空的充要条件是

$$
a,b,c\ge0,\qquad a+b+c\le1.
$$

满足这些条件时，置 $r_0=1-a-b-c$，全部相容概率恰为

$$
p(t)=(r_0-t,\ a,\ b,\ c,\ t),\qquad 0\le t\le r_0.
$$

其 $p_{13}$ 坐标宽度是 $r_0$，带符号隐藏方向为 $(1,0,0,0,-1)$ 的实倍数。若 $r_0>0$，纤维是非退化闭区间；若 $r_0=0$，纤维是一点；任一可行条件失败时纤维为空。

**证明。** 归一化强制 $p_0+p_{13}=r_0$。令 $t=p_{13}$，则 $p_0=r_0-t$，两项非负恰给所列区间；另外三项的非负性恰给 $a,b,c\ge0$。反向把这些分量代回即可。$\square$

故只有在此种读口下，剩余经典概率自由度才仅在空模式与联合模式之间反向转移。这里 $a,b,c$ 是概率数据，不是固定空间端点。

**命题 8.5（固定三个占位均值）。** 给定实数 $(X,Y,Z)$，其完整相容概率纤维非空的充要条件是

$$
(X,Y,Z)\in\mathcal P
:=\{X,Y,Z\ge0:\ X+Z\le1,\ Y+Z\le1\}.
$$

在此域内令

$$
r=1-Z,\qquad
\kappa_-=\max(0,X+Y-r),\qquad
\kappa_+=\min(X,Y).
$$

全部相容概率恰为

$$
p_\kappa=
(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad \kappa_-\le\kappa\le\kappa_+.
$$

其 $\kappa=p_{13}$ 坐标宽度为

$$
w=\kappa_+-\kappa_-=
\min\{X,Y,r-X,r-Y\}.
$$

归一化带符号概率超平面上的读出核为

$$
\mathbb R\nu,\qquad \nu=(1,-1,0,-1,1).
$$

在 $\mathcal P$ 内，$w>0$ 当且仅当 $r>0$ 且 $0<X,Y<r$；这时纤维为非退化区间。$w=0$ 当且仅当四个数 $X,Y,r-X,r-Y$ 至少一个为零，这时纤维是一点。特别地，$Z=1$ 强制 $X=Y=0$ 且 $p_2=1$。在 $\mathcal P$ 外纤维为空，不能把形式核线称为实际非空的一维纤维。

**证明。** 令 $\kappa=p_{13}$，占位方程依次给 $p_1=X-\kappa$、$p_3=Y-\kappa$、$p_2=Z$，归一化给 $p_0=r-X-Y+\kappa$。五项非负等价于

$$
Z\ge0,\qquad \max(0,X+Y-r)\le\kappa\le\min(X,Y).
$$

若区间非空，$\kappa\ge0$ 与 $\kappa\le X,Y$ 给 $X,Y\ge0$；而 $X+Y-r\le\kappa\le Y,X$ 给 $X,Y\le r$，因此数据在 $\mathcal P$。反之，在 $\mathcal P$ 内有 $0\le X,Y\le r$，从而下端点不超过上端点。单独写区间不等式时，不能遗漏 $Z\ge0$。

计算宽度可先设 $X\le Y$。若 $X+Y\le r$，则 $w=X$，且 $X$ 是上述四数的最小值；若 $X+Y\ge r$，则 $w=r-Y$，且它是四数的最小值。交换 $X,Y$ 得到全部情形。由四项非负，宽度的严格正性与零宽边界也随即成立。

若两个归一化实向量有相同占位，令其末分量之差为 $t$。占位方程使第一端、第三端分量差均为 $-t$，中模式分量差为零；归一化使空模式分量差为 $t$，故差为 $t\nu$。$\square$

这是 [B] 定理 3.3 和 [O] 命题 4.3 的同一反解。它与固定 $p_1,p_2,p_3$ 的纤维使用不同观察映射，隐藏方向也不同。若仪器实际逐样本保留完整三元占位记录 $(x,y,z)$，五种取值已区分全部模式，其总体联合律给出全部 $p_s$；仅保留三个均值则遗漏 $\kappa$。均值稳定不等于完整记录律稳定。

**命题 8.6（概率完整性与密度矩阵完整性）。** 记固定对角概率 $p$ 的密度矩阵集合为

$$
\mathcal D_p=\{\rho\ge0:\operatorname{Tr}\rho=1,\ \rho_{ss}=p_s\}.
$$

每个 $p\in\Delta^4$ 都有非空的 $\mathcal D_p$。它是一点当且仅当 $p$ 的支撑只有一个模式。因而一个概率纤维是一点，并不通常意味着其密度矩阵纤维也是一点；即使全部五个概率已给定，仍可留下相干区别。

**证明。** 对角矩阵 $\operatorname{diag}p$ 总是合法。正半定矩阵的二阶主子式给

$$
|\rho_{st}|^2\le p_sp_t.
$$

若 $p_s=0$，第 $s$ 行列的非对角项全为零；若支撑只有一个模式，故只能有相应的 $P_s$。反之，取 $p_s,p_t>0$ 和 $0<\delta\le\sqrt{p_sp_t}$，则

$$
\operatorname{diag}p\ \pm\delta
\bigl(|s\rangle\langle t|+|t\rangle\langle s|\bigr)
$$

具有非负的 $s,t$ 二阶块，其余是非负对角块，迹为一。这是两个不同的合法密度矩阵，且对角相同。$\square$

特别地，在任一上述单点概率纤维中，只要唯一概率仍支持至少两个模式，量子纤维就不是单点。限制制备到对角态或某个更小族会改变这一问题，须使用那个族自己的观察纤维。

### 8.3. 保持全部概率的联合相位轨道

**假设 8.7（相干制备与可调用门）。** 在同一个五模式载体上，供应均匀相干态和联合相位门

$$
|\psi_0\rangle=\frac{|0\rangle+|1\rangle+|2\rangle+|3\rangle+|13\rangle}{\sqrt5},
\qquad U_\theta=e^{-i\theta Q},\quad \theta\in\mathbb R.
$$

需要使用某个角度时，实际菜单须包含该角度的门及相应制备。$Q$ 作为效果存在，不自动供应其 Hamiltonian 或相位控制。这正是 [B] 命题 8.10、10.3 的资源条件。它们并未从原生替换算术或五个标签推出任意相位门。

**命题 8.8（精确离散轨道）。** 对所有整数 $N\ge0$，

$$
|\psi_N\rangle=U_\theta^N|\psi_0\rangle
=\frac{|0\rangle+|1\rangle+|2\rangle+|3\rangle+e^{-iN\theta}|13\rangle}{\sqrt5}.
$$

其全部五个概率均为 $1/5$，占位均值恒为 $(2/5,2/5,1/5)$。在四个底角振幅均非零的图上定义

$$
\zeta(\psi)=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}.
$$

则 $\zeta(\psi_N)=e^{-iN\theta}$。

**证明。** $Q$ 在 $|13\rangle$ 上取本征值一，在其余四个基向量上取零，因此 $U_\theta^N$ 只在联合模式上乘以 $e^{-iN\theta}$。各振幅模不变，范数平方仍为一。代入比值，分子、分母共同的 $1/5$ 消去，即得公式。$\square$

$\zeta$ 对共同非零复标量不变，因此是纯态射线上的关系坐标。它对应 [B] 定理 4.2 的 $\zeta=e^{\tau/2-i\chi}$；这里 $\tau=\log(p_0p_{13}/p_1p_3)=0$，$\chi=N\theta\pmod{2\pi}$。[B] 命题 10.3 的相位门参数在此取 $N\theta$；命题 8.10 用 $e^{+i\vartheta f}$ 时，取 $f=\mathbf1_{13}$、$\vartheta=-\theta$，故 $J_f=1$，符号一致。

四底角非零保证 $\zeta\in\mathbb C^\times$ 且其相位有定义。若分母为零，不使用此比值；若分子为零，也不把零的辐角当成关系相位。可用有定义的齐次乘积 $[\psi_0\psi_{13}:\psi_1\psi_3]$ 或支撑上的其他描述；两乘积同时为零时，连这个齐次对也无定义。对一般混态，不从五个对角概率选择一组振幅来定义一个唯一 $\zeta$。

为讨论相位参数，定义数学族

$$
|\psi(\phi)\rangle=\frac{|0\rangle+|1\rangle+|2\rangle+|3\rangle+e^{-i\phi}|13\rangle}{\sqrt5},\qquad \phi\in\mathbb R.
$$

离散轨道取 $\phi=N\theta$；此族的数学定义不供应离散菜单之外的制备。两射线 $[\psi(\phi)],[\psi(\phi')]$ 相同当且仅当 $\phi'-\phi\in2\pi\mathbb Z$：前四个非零振幅固定，强制共同相位为一，末分量再给此条件。若 $\theta/(2\pi)=p/q$ 为最简有理数，离散态序列的最小正周期是 $q$；若该比值无理，则无正整数周期。$N$ 在此只是门的重复次数，无须先指定连续外部时间。

### 8.4. 端点脉冲把相位返回原占位读口

**假设 8.9（指定端点控制）。** 供应

$$
H_1=|0\rangle\langle1|+|1\rangle\langle0|
+|3\rangle\langle13|+|13\rangle\langle3|,
\qquad R_1(\alpha)=e^{-i\alpha H_1}.
$$

它是 [B] 命题 8.9 中 $G_1=X_1P_2^0$ 在合法五态子空间上的限制：逐个作用于位串，得到 $0\leftrightarrow1$、$3\leftrightarrow13$，并湮灭 $|2\rangle$。因此其指数固定 $|2\rangle$、保持五态子空间，无须先测量中位。这里 $H_1$ 是无量纲归一化生成元；若物理 Hamiltonian 为 $gH_1$ 且作用时长为 $t$，则 $\alpha=gt/\hbar$，这些物理量须另供。

**命题 8.10（完整振幅和概率计算）。** 令 $c_\alpha=\cos\alpha$、$s_\alpha=\sin\alpha$。在 $(0,1)$ 与 $(3,13)$ 两个有序二阶块上，脉冲矩阵均为

$$
\begin{pmatrix}c_\alpha&-is_\alpha\\-is_\alpha&c_\alpha\end{pmatrix}.
$$

对 $\psi(\phi)$，脉冲后的五个振幅依次为

$$
\frac1{\sqrt5}
\bigl(c_\alpha-is_\alpha,\ c_\alpha-is_\alpha,\ 1,
\ c_\alpha-is_\alpha e^{-i\phi},\ c_\alpha e^{-i\phi}-is_\alpha\bigr).
$$

因而完整概率为

$$
p_0'=p_1'=p_2'=\frac15,\qquad
p_3'=\frac{1-\sin(2\alpha)\sin\phi}{5},\qquad
p_{13}'=\frac{1+\sin(2\alpha)\sin\phi}{5},
$$

并有

$$
X_\phi(\alpha)=\frac25+\frac15\sin(2\alpha)\sin\phi,
\qquad Y_\phi(\alpha)=\frac25,\qquad Z_\phi(\alpha)=\frac15.
$$

**证明。** 在每个二阶块中 $H_1^2=I_2$，指数的奇偶幂分别求和得到所列矩阵；中央块的指数为一。逐块乘上输入振幅即得完整输出。前两项的模平方为 $(c_\alpha^2+s_\alpha^2)/5=1/5$。末项中

$$
|c_\alpha e^{-i\phi}-is_\alpha|^2
=c_\alpha^2+s_\alpha^2+2c_\alpha s_\alpha\sin\phi
=1+\sin(2\alpha)\sin\phi.
$$

另一项给相反符号。所有分量非负，因为 $|\sin(2\alpha)\sin\phi|\le1$，且总和为一。取 $X'=p_1'+p_{13}'$ 得公式；$Y'=p_3'+p_{13}'$ 是第二块总质量，$Z'=p_2'$ 是固定中央质量。$\square$

**例 8.11（同当前读数而不同未来读数）。** 若菜单供应 $\theta=\pi/2$ 的联合相位门和 $\alpha=\pi/4$ 的端点脉冲，取 $N=0$ 与 $N=1$ 的两个准备。它们当前全部五个模式概率相同，均为 $1/5$；当前三个占位均值也相同。但施加同一个端点脉冲后，前者的占位是

$$
(2/5,2/5,1/5),
$$

后者的占位是

$$
(3/5,2/5,1/5),
$$

后者的完整概率为 $(1/5,1/5,1/5,0,2/5)$。两输出均合法。一般地，任意两个相位的未来差是

$$
\Delta X=\frac{\sin(2\alpha)}5(\sin\phi-\sin\phi'),
\qquad \Delta Y=\Delta Z=0.
$$

**命题 8.12（此读法的盲角与别名）。** 若 $\sin(2\alpha)=0$，即 $\alpha\in(\pi/2)\mathbb Z$，此脉冲对整个均匀相位族的末端占位都不敏感。若 $\sin(2\alpha)\ne0$，两个相位给相同末端三均值的充要条件是

$$
\sin\phi=\sin\phi'
\iff
\phi'\equiv\phi\ \text{或}\ \pi-\phi\pmod{2\pi}.
$$

因此这一读法只取得正弦，不唯一确定圆上的完整相位；例如 $\phi=0$ 与 $\phi=\pi$ 是不同态，却给同一响应。非盲脉冲下，响应回到基值 $X=2/5$ 当且仅当 $\phi\in\pi\mathbb Z$。对于固定 $\theta\in\pi\mathbb Z$，全部整数步的正弦都为零；若 $\theta\notin\pi\mathbb Z$，$N=0,1$ 已可由任一非盲脉冲区分。

**证明。** 由差式先分离 $\sin(2\alpha)=0$ 的情形。在另一情形用

$$
\sin\phi-\sin\phi'
=2\cos\frac{\phi+\phi'}2\sin\frac{\phi-\phi'}2
$$

得两类别名，其余结论由正弦零点得到。$\square$

端点脉冲作为五维酉矩阵以 $2\pi$ 为周期；其对上述末端概率的作用以 $\pi$ 为周期。若另外知道制备相位、门参数及重复次数，控制历史已可确定 $N\theta\pmod{2\pi}$。所证明的不足性仅针对当前统计摘要，不是说完整已知控制历史也不含相位信息。

**例 8.13（插入破坏性测量改变任务）。** 若在端点脉冲前实际执行模式投影测量并丢弃输出，其平均更新为

$$
\Delta(\rho)=\sum_sP_s\rho P_s.
$$

对上述所有相位态，$\Delta(|\psi(\phi)\rangle\langle\psi(\phi)|)=I_5/5$。再施加任意 $R_1(\alpha)$，仍得 $I_5/5$，于是没有相位响应。证明只是去掉全部非对角项并使用酉共轭保持单位阵。这说明“每步精确知道五个总体概率”和“在同一份相干输入上逐步实际测量模式”不是同一协议；测量即使使用与相位门对易的效果，也不能据此假定保留所需相干。

### 8.5. 对角关系能量与连续相位速度

**假设 8.14（另供的连续动力学）。** 固定实能量 $E_s$、$\hbar>0$ 和时间不变的对角 Hamiltonian

$$
H=\sum_{s\in\Sigma}E_sP_s.
$$

它是独立的动力学输入。模式的存在、空模式的“自身”解释或联合模式的“预测”解释，都不决定这些能量或实际时钟。

**应用 8.15（五点函数展开的能量版本）。** [B] 定理 3.2 取 $f_s=E_s$，得到唯一展开

$$
H=E_0I+(E_1-E_0)N_x+(E_3-E_0)N_y+(E_2-E_0)N_z+JQ,
$$

其中

$$
J=E_{13}-E_1-E_3+E_0.
$$

**证明。** 将右侧依次作用于 $|0\rangle,|1\rangle,|3\rangle,|2\rangle$，其本征值分别强制常数项为 $E_0$，三个占位系数为 $E_1-E_0,E_3-E_0,E_2-E_0$；在 $|13\rangle$ 上比较，剩余系数被强制为 $J$。这些五个基向量张成 $\mathcal H$，故展开存在且唯一。$\square$

$J$ 是底面四角的混合差分，度量不能由公共能量和两个分别占位项表达的联合能量部分。它不包括由 $E_2-E_0$ 单独确定的中央模式能量。对固定占位纤维，

$$
\operatorname{Tr}(H\rho)
=E_0+(E_1-E_0)X+(E_3-E_0)Y+(E_2-E_0)Z+J\kappa.
$$

所以该纤维的平均能量范围宽度为 $|J|w$；仅在 $w>0$ 且 $J\ne0$ 时，经典隐藏自由度才使平均能量不唯一。这个平均能量差与下述固定概率上的相干演化是不同机制。

**命题 8.16（连续相位演化）。** 纯态按 $e^{-iHt/\hbar}$ 演化时，每个模式概率保持不变。在四个底角初始振幅均非零的条件下，对全部实数 $t$ 有

$$
\zeta(t)=\zeta(0)e^{-iJt/\hbar},
\qquad
\frac{d\zeta}{dt}=-\frac{iJ}{\hbar}\zeta.
$$

若在连续时间的一个区间内选择辐角提升，则

$$
\frac{d}{dt}\arg\zeta=-\frac J\hbar.
$$

按 [B] 的 $\zeta=e^{\tau/2-i\chi}$ 记号，等价地 $\dot\chi=J/\hbar$，$\tau$ 不变。

**证明。** 各振幅满足

$$
\psi_s(t)=e^{-iE_st/\hbar}\psi_s(0).
$$

相位因子模为一，故概率和非零支撑均不变。代入关系比值得

$$
\frac{\psi_0(t)\psi_{13}(t)}{\psi_1(t)\psi_3(t)}
=\frac{\psi_0(0)\psi_{13}(0)}{\psi_1(0)\psi_3(0)}
\exp\!\left[-\frac{i}{\hbar}(E_0+E_{13}-E_1-E_3)t\right].
$$

括号中的能量正是 $J$，微分即得速度公式。$\square$

对 $J\ne0$，此非零关系坐标的连续周期是 $2\pi\hbar/|J|$，相位仍只按 $2\pi$ 识别。若底角振幅为零，概率不变的结论仍成立，但不把该比值或辐角公式延伸到无定义处。

**例 8.17（离散门与连续模型的精确对应）。** 对 $H=JQ$，有

$$
e^{-iHt/\hbar}=U_{Jt/\hbar}.
$$

均匀初态在任意时刻的五个概率仍为 $1/5$，端点脉冲后

$$
X(t,\alpha)=\frac25+\frac15\sin(2\alpha)\sin(Jt/\hbar),
\qquad Y=\frac25,\qquad Z=\frac15.
$$

若另给每步时长 $\Delta t$，则 $\theta=J\Delta t/\hbar$、$t=N\Delta t$，准确回到离散公式。此处相互作用能量表现为当前概率遗漏的关系相位变化；需要所声明的 Hamiltonian 和后续控制，才有物理势能及其读出的解释。

对一般对角 $H$，$J$ 只单独控制 $\zeta$ 的关系速度，不单独确定任意端点响应。以均匀初态为例，直接使用两个二阶块给

$$
X(t,\alpha)=\frac25+\frac{\sin(2\alpha)}5
\left[
\sin\frac{(E_1-E_0)t}{\hbar}
+\sin\frac{(E_{13}-E_3)t}{\hbar}
\right],\qquad Y=\frac25,\quad Z=\frac15.
$$

**证明。** 对任意一对输入振幅 $e^{-iE_at/\hbar}/\sqrt5,e^{-iE_bt/\hbar}/\sqrt5$，取出共同相位后，第二个分量正是前述计算中的 $e^{-i\phi}/\sqrt5$，其中 $\phi=(E_b-E_a)t/\hbar$。因此被 $N_x$ 读取的该对第二项概率为 $[1+\sin(2\alpha)\sin\phi]/5$；将两对相加即得公式，块总质量与中央质量仍不变。$\square$

两个跃迁频率的差为 $J/\hbar$，但它们的正弦响应还可能相消。因此不能在未消除其他能量项时，把一般 $H$ 的此脉冲响应直接写成只依赖 $J$ 的单正弦。

**反例 8.18（$J=0$ 不意味着完整态静止）。** 取 $\Delta\ne0$，令 $H=\Delta N_x$。即

$$
E_0=E_2=E_3=0,\qquad E_1=E_{13}=\Delta,
$$

于是 $J=0$。对均匀初态，$\zeta(t)=1$，全部概率不变，但

$$
\rho_{01}(t)=\frac15e^{i\Delta t/\hbar}
$$

随时间变化。一般混态的矩阵元满足

$$
\rho_{st}(t)=e^{-i(E_s-E_t)t/\hbar}\rho_{st}(0).
$$

故完整密度矩阵在所有时间静止，当且仅当 $(E_s-E_t)\rho_{st}(0)=0$ 对全部 $s,t$ 成立，亦即 $[H,\rho(0)]=0$。因此 $J=0$ 固定上述关系坐标，却不足以保证完整态静止；反过来，能量对角混态即使 $J\ne0$ 也可静止。一次离散时刻的偶然回归也不等于所有时间静止。

### 8.6. 当前均值能否预测未来：已有下降判据的效果空间应用

**定义 8.19（当前效果空间）。** 在五维模型中取

$$
\mathcal W=\operatorname{span}_{\mathbb R}\{I,N_x,N_y,N_z\}
\subseteq\operatorname{Herm}(\mathcal H).
$$

它是四维实线性空间，包含单位阵；其元素是测得效果的实线性组合，不要求每个元素本身都是 $[0,I]$ 内的事件效果。两个态在当前三均值下相同，当且仅当它们对全部 $A\in\mathcal W$ 的期望相同。以下 Hilbert–Schmidt 内积不归一化：

$$
\langle A,B\rangle_{\mathrm{HS}}=\operatorname{Tr}(AB)
\quad(A,B\ \text{Hermitian}),\qquad
\|A\|_{\mathrm{HS}}^2=\operatorname{Tr}(A^\dagger A).
$$

**应用 8.20（全部密度矩阵上的精确一步预测）。** 固定一个对所有待比较输入都合法且实际供应的酉操作 $U$。存在仅依赖当前三个均值、对全部输入密度矩阵都准确预测 $U$ 后同组三均值的函数，当且仅当

$$
U^\dagger\mathcal WU\subseteq\mathcal W.
$$

函数不必事先要求线性；包含关系成立时可选择当前读数的仿射函数。这里应用 [B] 定理 7.3，而不是增加一个新的通用下降原理。精确参数对应为

$$
V=\operatorname{Herm}(\mathcal H),\qquad
L(X)=\bigl(\operatorname{Tr}X,\operatorname{Tr}(N_xX),
\operatorname{Tr}(N_yX),\operatorname{Tr}(N_zX)\bigr),
\qquad T(X)=UXU^\dagger.
$$

该定理的读出核 $\ker L$ 正是 $\mathcal W^\perp$；核保持 $T(\ker L)\subseteq\ker L$ 经迹对偶化，就是上述效果空间包含关系。

**普通应用证明。** 若包含关系成立，对每个读口 $A_j\in\{N_x,N_y,N_z\}$ 可写

$$
U^\dagger A_jU=c_{j0}I+c_{jx}N_x+c_{jy}N_y+c_{jz}N_z,
$$

因此未来读数为 $c_{j0}+c_{jx}X+c_{jy}Y+c_{jz}Z$，对任意输入态有效。

反过来，若包含关系失败，则至少一个实际读口 $A_j$ 的拉回 $B=U^\dagger A_jU$ 不在 $\mathcal W$；否则所有生成元的拉回都在其中，包含关系不会失败。取其正交残差

$$
D=P_{\mathcal W^\perp}B\ne0.
$$

$D$ 是 Hermitian，且因 $I\in\mathcal W$ 而满足 $\operatorname{Tr}D=0$。写 $d=\dim\mathcal H$（此处 $d=5$），任选

$$
0<\varepsilon\le\frac1{d\|D\|_{\mathrm{op}}},\qquad
\rho_\pm=\frac{I_d}{d}\pm\varepsilon D.
$$

对每个向量 $v$，

$$
\langle v,\rho_\pm v\rangle
\ge\left(\frac1d-\varepsilon\|D\|_{\mathrm{op}}\right)\|v\|^2\ge0,
\qquad \operatorname{Tr}\rho_\pm=1.
$$

故两者是合法密度矩阵；严格小于上界时正定。对所有 $A\in\mathcal W$，其当前期望差为 $2\varepsilon\operatorname{Tr}(AD)=0$。但由于 $B=P_{\mathcal W}B+D$，正交性给

$$
\operatorname{Tr}[A_jU(\rho_+-\rho_-)U^\dagger]
=2\varepsilon\operatorname{Tr}(BD)
=2\varepsilon\|D\|_{\mathrm{HS}}^2>0.
$$

同一当前读数因此对应两个不同未来读数，连非线性预测器也不能同时正确。这给出全部输入量词下的必要性，以及有明确正性半径的见证。$\square$

**约定 8.21（受限制备与操作合法性）。** 若只允许某个制备族 $\mathcal S\subsetneq\mathcal D(\mathcal H)$，恰当条件是

$$
\mathcal O(\rho)=\mathcal O(\sigma)
\Longrightarrow
\mathcal O(U\rho U^\dagger)=\mathcal O(U\sigma U^\dagger)
\qquad(\rho,\sigma\in\mathcal S).
$$

全空间的包含关系仍充分，却未必必要，因为上述内点状态对可能不在 $\mathcal S$。若合法菜单依赖输入，还须保证待比较状态上操作的可调用性也在相应观察纤维上相同，或把已知合法性信息并入观察；不能对一个状态合法、另一个不合法的门直接要求共同未来预测。有限步序列的论证也必须使用每一步实际可达的来源域。

### 8.7. 实际端点脉冲的闭包残差及其消费者

**命题 8.22（$H_1$ 拉回的精确非对角部分）。** 定义 Hermitian 矩阵

$$
K=i\bigl(|0\rangle\langle1|-|1\rangle\langle0|
+|3\rangle\langle13|-|13\rangle\langle3|\bigr).
$$

则

$$
K^2=I-N_z,\qquad \operatorname{Tr}K=0,\qquad
K\perp\mathcal W,\qquad \|K\|_{\mathrm{HS}}^2=4.
$$

对任意实数 $\alpha$，

$$
B_\alpha:=R_1(\alpha)^\dagger N_xR_1(\alpha)
=\sin^2\alpha\,(I-N_z)+\cos(2\alpha)N_x
+\frac{\sin(2\alpha)}2K,
$$

而

$$
R_1(\alpha)^\dagger N_yR_1(\alpha)=N_y,
\qquad R_1(\alpha)^\dagger N_zR_1(\alpha)=N_z.
$$

所以 $B_\alpha$ 在 $\mathcal W^\perp$ 上的正交残差及其范数恰为

$$
D_\alpha=\frac{\sin(2\alpha)}2K,\qquad
\|D_\alpha\|_{\mathrm{HS}}^2=\sin^2(2\alpha),\qquad
\|D_\alpha\|_{\mathrm{op}}=\frac{|\sin(2\alpha)|}2.
$$

特别地，对全部密度矩阵，端点脉冲保持当前效果空间的充要条件是

$$
R_1(\alpha)^\dagger\mathcal WR_1(\alpha)\subseteq\mathcal W
\iff\sin(2\alpha)=0.
$$

**证明。** 在每个 $(a,b)=(0,1),(3,13)$ 有序块上，$N_x$ 限制为 $\operatorname{diag}(0,1)$，所以

$$
\begin{pmatrix}c_\alpha&is_\alpha\\is_\alpha&c_\alpha\end{pmatrix}
\begin{pmatrix}0&0\\0&1\end{pmatrix}
\begin{pmatrix}c_\alpha&-is_\alpha\\-is_\alpha&c_\alpha\end{pmatrix}
=
\begin{pmatrix}s_\alpha^2&is_\alpha c_\alpha\\-is_\alpha c_\alpha&c_\alpha^2\end{pmatrix}.
$$

对角部分为 $s_\alpha^2I_2+\cos(2\alpha)\operatorname{diag}(0,1)$，非对角部分为 $[\sin(2\alpha)/2]\begin{pmatrix}0&i\\-i&0\end{pmatrix}$。中央块为零，两个块相加得到 $B_\alpha$。

$K$ 的每个二阶块平方是 $I_2$，中央块是零，故 $K^2=I-N_z$；其全部对角元为零，因此与对角空间 $\mathcal W$ 正交，且平方迹为四。$B_\alpha$ 的其余项已经在 $\mathcal W$ 中，所以所列非对角项就是正交残差，两个范数公式由 $K$ 的本征值 $1,1,-1,-1,0$ 得到。

$N_y$ 是第二块上的单位、第一块和中央块上的零，故被脉冲固定；$N_z$ 也固定。当 $\sin(2\alpha)=0$，全部生成元拉回均在 $\mathcal W$ 中；当其非零，$B_\alpha$ 的非零残差排除包含关系。$\square$

这给 [B] 命题 10.4 的闭包残差一个实际消费者：检测的对象是所供应端点门对 $N_x$ 的具体拉回，不是从一般“隐藏关系”名称推断泄漏。

**例 8.23（显式、统一合法的密度矩阵对）。** 对非盲角 $\sin(2\alpha)\ne0$，取

$$
\rho_\pm=\frac{I_5}{5}\pm\frac{D_\alpha}{5}.
$$

它们的迹为一，全部五个对角概率为 $1/5$。四个底面本征值是

$$
\frac15+\frac{\sin(2\alpha)}{10},\quad
\frac15-\frac{\sin(2\alpha)}{10},
$$

各重复两次；中央本征值是 $1/5$。故所有本征值至少 $1/10$，两者均正定，且不同。当前三均值均为 $(2/5,2/5,1/5)$，而脉冲后的 $N_x$ 期望分别为

$$
\operatorname{Tr}(B_\alpha\rho_\pm)
=\frac25\pm\frac{\sin^2(2\alpha)}5.
$$

差为 $2\sin^2(2\alpha)/5>0$；未来 $N_y,N_z$ 仍相同。这正是前述一般见证在 $d=5$、$\varepsilon=1/5$ 的合法实例，给出明确的归一化、正性及可读分离。

同一个残差也直接消费前面的相干相位族。逐块计算有

$$
\langle\psi(\phi)|K|\psi(\phi)\rangle=\frac25\sin\phi.
$$

第一块的两个相同振幅贡献零；第二块贡献
$i(e^{-i\phi}-e^{i\phi})/5=2\sin\phi/5$。因此在 $B_\alpha$ 分解中，对角部分贡献 $2/5$，残差部分贡献 $\sin(2\alpha)\sin\phi/5$，准确重现端点响应的符号与系数。

对只允许对角输入的单次任务，$\operatorname{Tr}(K\rho)=0$，于是即使角度非盲，仍有

$$
X'=\sin^2\alpha\,(1-Z)+\cos(2\alpha)X,\qquad Y'=Y,\quad Z'=Z.
$$

这说明受限制备下均值可预测与全密度矩阵上的效果空间闭合有不同量词。脉冲输出一般已经不再对角，不能据此把同一制备限制未经检查地沿任意后续序列重复使用。

### 8.8. 菜单、末端均值与完整仪器记录

**应用 8.24（所供酉菜单的预测范围）。** 联合相位门及任意对角 $e^{-iHt/\hbar}$ 都与 $I,N_x,N_y,N_z$ 交换，故保持 $\mathcal W$。若所允许的全部酉生成元都保持 $\mathcal W$，则每个有限合法字也保持它：两个操作的复合 $VU$ 满足

$$
(VU)^\dagger\mathcal W(VU)
=U^\dagger(V^\dagger\mathcal WV)U\subseteq\mathcal W,
$$

逐次归纳即可。反之，若菜单含一个非盲的 $R_1(\alpha)$，上述正定态对已使当前三均值不足以预测全部允许末端均值。若菜单只含对角门和盲角端点门，则这个较小菜单确实闭合。此处每一结论都相对于实际供应的菜单；不从此推断原生全可控性、额外相位层析资源或无限精度取得能力。

可以定义当前被合并的区别具有相对于菜单 $\mathfrak M$ 的“未来返回能力”，是指存在同一当前纤维中的两态 $\rho,\sigma$、共同合法的有限操作字 $w$ 和一个指定末端读口 $A$，使

$$
\operatorname{Tr}(A\,U_w\rho U_w^\dagger)
\ne\operatorname{Tr}(A\,U_w\sigma U_w^\dagger).
$$

这是预测上的可区分性条件。若使用“势能”一词，仍须另供前述能量单位与 Hamiltonian。一个操作下无分离不等于所有允许未来都无分离；一个非闭合见证也不说明每一对隐藏态都可由同一探针分离。

**定义 8.25（输出解析记录任务）。** 固定有限动作集、每个动作的有限输出集，以及包含 $I$ 的有限末端效果族。若过程含实际仪器，令每个动作 $a$ 对应完全正映射族 $\{\Phi_{a,o}\}_o$，其和保迹；联合载体须包含本任务依赖的保留环境或仪器记忆。对时间顺序的词

$$
h=((a_1,o_1),\ldots,(a_m,o_m)),\qquad
\Phi_h=\Phi_{a_m,o_m}\circ\cdots\circ\Phi_{a_1,o_1},
$$

有记录与末端效果 $0\le G\le I$ 的联合概率

$$
p_\rho(h,G)=\operatorname{Tr}[G\Phi_h(\rho)]
=\operatorname{Tr}[\Phi_h^*(G)\rho].
$$

若需记录后的条件态，仅在 $p_\rho(h,I)>0$ 时定义 $\Phi_h(\rho)/p_\rho(h,I)$。

[B] 定义 8.3、定理 8.4 和 [C] 的逐输出闭包供应此任务的现成判据：保留所有实际分支拉回 $\Phi_h^*(G)$ 的线性张成，才能检验全部记录统计。具体地，两态的全部上述联合概率相同，当且仅当其差与每个 $\Phi_h^*(G)$ 正交；这由所列迹差逐项为零及线性张成立即得到。若当前摘要含末端效果且对每个分支拉回不变，则所有有限词效果都在该摘要中，归纳即给充分性。

只检查平均通道 $\sum_o\Phi_{a,o}$ 的不变性，只涉及丢弃输出后的相应任务，不能替代逐分支条件。例如，对模式测量 $\Phi_s(\rho)=P_s\rho P_s$，平均去相干通道固定 $\mathcal W$，但单分支 $13$ 的拉回为

$$
\Phi_{13}^*(I)=Q\notin\mathcal W.
$$

$Q$ 不在其中可逐模式检验：若 $Q=aI+bN_x+cN_y+dN_z$，在 $0,1,3,2$ 上依次得到 $a=b=c=d=0$，与其在 $13$ 上为一矛盾。故同一非退化占位纤维中的不同 $\kappa$ 会给不同模式输出律，尽管平均通道保持当前三均值。

反之，前面的均匀相位对甚至有相同完整模式分布，模式测量仍不能读取它们的相位。完整模式概率、实际模式记录、相干未来、已知控制历史各自保留不同信息，须按所声明任务比较。反馈策略也只能使用已经取得的输出前缀；不能把隐态信息作为免费控制条件。

### 8.9. 固定标架的局部量子位与变化的联合关系

**约定 8.26（独立供应的复合系统）。** 本节另给 $\mathcal H_A=\mathbb C^2$、$\mathcal H_B=\mathbb C^2$，以及实际复合载体 $\mathcal H_A\otimes\mathcal H_B$。这是一个单独的量子模型；五维空间本身不能被识别为两个量子位的四维张量积。对五模式底面做编码也须另给具体等距映射与控制合同，不能从模式 $13$ 的标签取得该资源。

**应用 8.27（已有局部 Bloch 接口的唯一性）。** 固定基、标架与测量标定，令

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

任意量子位密度矩阵唯一表示为

$$
\rho_A=\frac12(I_2+x\sigma_x+y\sigma_y+z\sigma_z),\qquad
x=\operatorname{Tr}(\sigma_x\rho_A),\quad
 y=\operatorname{Tr}(\sigma_y\rho_A),\quad
 z=\operatorname{Tr}(\sigma_z\rho_A),
$$

且其合法域恰为 $x^2+y^2+z^2\le1$。因此同一固定标架中的三个 Pauli 总体期望严格不变，确实强制局部密度矩阵不变。

**普通应用证明。** $I_2,\sigma_x,\sigma_y,\sigma_z$ 是二维 Hermitian 矩阵实空间的一组基，满足

$$
\operatorname{Tr}\sigma_j=0,\qquad
\operatorname{Tr}(\sigma_j\sigma_k)=2\delta_{jk}.
$$

一般 Hermitian 矩阵先按此基展开，迹一固定单位项系数为 $1/2$，再与各 $\sigma_j$ 取迹，强制其余系数为 $x/2,y/2,z/2$，证明存在且唯一。Pauli 乘法给

$$
(x\sigma_x+y\sigma_y+z\sigma_z)^2=(x^2+y^2+z^2)I_2,
$$

因此 $\rho_A$ 的本征值为 $(1\pm\sqrt{x^2+y^2+z^2})/2$，正半定当且仅当该向量落在单位球内。$\square$

这就是 [L] 定义 9.1 所消费的局部 Bloch 供应接口，其标准 Bloch 球及混态球解释见 IBM Quantum Learning [IBM]。该接口中 $r_x,r_y,r_z$ 在此分别为 $x,y,z$；这里的 Pauli 期望不是五模式的占位均值 $X,Y,Z$，也不是位置坐标。尤其不能在这组信息完备的局部读口之外，再宣称同一个局部密度矩阵中仍有未读出的额外密度参数。

这一唯一性不提供在一份未知输入上同时无损取得三个精确数的仪器。Pauli 效果不对易；并且各方差为 $1-x^2,1-y^2,1-z^2$，总和 $3-x^2-y^2-z^2\ge2$。三个总体期望的重建需要相应制备与测量资源。它也不确定一个混态的唯一纯态集合分解、产生它的全部历史或环境联合态。

**命题 8.28（局部恒定而 Bell 相位相关变化）。** 在所供复合系统中，令

$$
|\Phi_\varphi\rangle=\frac{|00\rangle+e^{i\varphi}|11\rangle}{\sqrt2},
\qquad \rho_{AB}(\varphi)=|\Phi_\varphi\rangle\langle\Phi_\varphi|.
$$

对所有实数 $\varphi$，

$$
\rho_A(\varphi)=\operatorname{Tr}_B\rho_{AB}(\varphi)=\frac{I_2}{2},
\qquad
\rho_B(\varphi)=\operatorname{Tr}_A\rho_{AB}(\varphi)=\frac{I_2}{2},
$$

所以两边各自的三个 Pauli 期望全为零，但

$$
\langle\sigma_x\otimes\sigma_x\rangle_\varphi=\cos\varphi,
\qquad
\langle\sigma_x\otimes\sigma_y\rangle_\varphi=\sin\varphi.
$$

**证明。** 将密度矩阵展开为

$$
\rho_{AB}(\varphi)=\frac12\bigl(
|00\rangle\langle00|+|11\rangle\langle11|
+e^{-i\varphi}|00\rangle\langle11|
+e^{i\varphi}|11\rangle\langle00|\bigr).
$$

部分迹对交叉项给零，例如
$\operatorname{Tr}_B(|00\rangle\langle11|)=|0\rangle\langle1|\langle1|0\rangle=0$；两对角项分别留下 $|0\rangle\langle0|/2$ 与 $|1\rangle\langle1|/2$，故两约化态均为 $I_2/2$。Pauli 矩阵无迹，局部期望因而为零。

$\sigma_x\otimes\sigma_x$ 交换 $|00\rangle,|11\rangle$，所以其期望为 $(e^{i\varphi}+e^{-i\varphi})/2=\cos\varphi$。而

$$
(\sigma_x\otimes\sigma_y)|00\rangle=i|11\rangle,\qquad
(\sigma_x\otimes\sigma_y)|11\rangle=-i|00\rangle,
$$

其期望为 $(-ie^{i\varphi}+ie^{-i\varphi})/2=\sin\varphi$。态范数为一，外积自动正半定且迹一。$\square$

若另行供应 $I_A\otimes\operatorname{diag}(1,e^{i\omega t})$，它把 $\Phi_0$ 送为 $\Phi_{\omega t}$，构成两个局部态恒定而联合相关连续变化的明确动力学路径。相位演化是否实际可调用，仍是操作输入。

**命题 8.29（相关读数所需的实际联合访问）。** 若允许对同一联合制备的一对系统分别测量 Pauli 并保留配对输出 $a,b\in\{-1,1\}$，则

$$
\Pr(a,b\mid x,x)=\frac14(1+ab\cos\varphi),\qquad
\Pr(a,b\mid x,y)=\frac14(1+ab\sin\varphi).
$$

边缘输出在两种设置下都均匀，与相位无关。对限定的 Bell 相位族，取得这两组相关总体量可确定 $\varphi\pmod{2\pi}$；仅一组余弦或正弦各自都有别名。该辨识结论不延伸为任意两量子位态的完整层析。

**证明。** 对设置 $(j,k)$，联合效果是

$$
\frac{I_2+a\sigma_j}{2}\otimes\frac{I_2+b\sigma_k}{2}.
$$

展开取期望，两个局部一阶项均为零，余下常数项与 $ab$ 倍的上述联合相关，得到公式。各概率非负并求和为一，边缘求和为 $1/2$。余弦与正弦同时给出单位圆上的点，故在该一参数族上确定模 $2\pi$ 的相位。$\square$

配对记录须来自同一联合态，不能把两个边缘统计拼成未取得的联合分布；两种不同设置的总体量也不声称在一份输入上同时精确测得。如果只访问 $A$，任何固定局部仪器的概率仅依赖 $\rho_A=I_2/2$，因此不能区分此族；局部后处理不能补回被部分迹合并的区别。若要把联合区别转成单边响应，须另外供应合适的联合控制或信息通道。[L] 定义 9.3 给出同一保留环境上 CNOT 返回的既有接口，但不能把换新环境的协议当成同一操作。

故“知道自身局部态”与“知道自身与环境的联合关系”是两项不同的识别任务。前者在固定量子位模型中可由三 Pauli 期望完整确定，后者仍可在相同局部态上变化；这不把“联合关系中的位置”解释为未经供应的几何空间位置。

### 8.10. 非负光谱、被动滤光与返回的三路差异

**定义 8.30（线性光谱读口）。** 给定波长测度空间 $(\Lambda,\mu)$，来源光谱取 $S\in L^1(\Lambda,\mu)$、$S\ge0$。给定三个实值本质有界灵敏度函数 $s_i\in L^\infty$，定义

$$
C_i(S)=\int_\Lambda s_i(\lambda)S(\lambda)\,d\mu(\lambda),
\qquad i=1,2,3.
$$

这保证每个读数绝对可积；若用非负探测器强度解释这些坐标，可再要求 $s_i\ge0$。此处不要求三个灵敏度互相正交或支撑不交。固定读口、色度系统和照明等比较条件，是解释同色异谱时的一部分输入。

CIE 的词条 [CIE] 将 metameric colour stimuli 定义为在指定色度系统中三刺激值相同而光谱不同的颜色刺激，其性质称为 metamerism。下述线性核论证表达这一结构；具体灵敏度是否是某个实际 CIE 标准观察者或经标定的仪器响应，须由对应数据给出。

**命题 8.31（合法光谱对与滤光后的差式）。** 设 $h\in L^1$ 满足

$$
\int s_i h\,d\mu=0\qquad(i=1,2,3),
$$

且 $S\ge0$、$S+h\ge0$ 几乎处处。则两合法光谱当前三路读数相同。若实际另供一个不混合波长的线性被动滤光器，其透射率 $a\in L^\infty$ 满足

$$
0\le a(\lambda)\le1\quad\text{几乎处处},
\qquad T_a(S)=aS,
$$

则两个输出仍非负且可积，并且差为

$$
\Delta C_i'=C_i(T_a(S+h))-C_i(T_aS)
=\int s_i a h\,d\mu.
$$

同一光谱对在这个滤光器后被区分，当且仅当至少一个积分非零。

**证明。** 初始差由积分线性性给 $C_i(S+h)-C_i(S)=\int s_i h=0$。乘以 $0\le a\le1$ 保持非负，并由 $|aS|\le|S|$、$|a(S+h)|\le|S+h|$ 保证可积。再次使用线性性得到输出差式及其非零充要条件。$\square$

非零 $h$ 在整个线性空间中存在，不保证任意选择的 $S$ 与 $S+h$ 都合法；逐点非负性必须核对。类似地，滤光器非恒定本身不保证区分。如果 $a=a_0$ 为常数，输出差恒为 $a_0\int s_i h=0$；如果 $a$ 在相关支撑上为零，或给定 $h$ 仍与所有 $a s_i$ 正交，也没有返回差异。更强的充分盲条件是每个 $a s_i$ 都在当前灵敏度的实线性张成内，此时对每个当前核方向 $h$ 都仍有零返回。

这里是绝对三路线性读数，未在滤光后按总功率重新归一化。滤光通常减少总光强；若读口改成归一化色度、另换照明、加入荧光或波长混合，必须使用相应的新模型，不能直接套用同一个乘法差式。

**例 8.32（四个波段上的严格非零返回）。** 取 $\Lambda=[0,4)$ 及 Lebesgue 测度，令

$$
B_1=[0,1),\quad B_2=[1,2),\quad B_3=[2,3),\quad B_4=[3,4).
$$

各波段测度为一，记指示函数为 $\mathbf1_{B_j}$，取三个非负有界灵敏度

$$
s_1=\mathbf1_{B_1}+\mathbf1_{B_4},\quad
s_2=\mathbf1_{B_2}+\mathbf1_{B_4},\quad
s_3=\mathbf1_{B_3}+\mathbf1_{B_4}.
$$

取 $0<\eta\le1$，定义两光谱

$$
S_0=\sum_{j=1}^4\mathbf1_{B_j},\qquad
h=-\mathbf1_{B_1}-\mathbf1_{B_2}-\mathbf1_{B_3}+\mathbf1_{B_4},
\qquad S_\eta=S_0+\eta h.
$$

其四波段值分别为

$$
S_0:(1,1,1,1),\qquad
S_\eta:(1-\eta,1-\eta,1-\eta,1+\eta).
$$

这些值非负；$\eta<1$ 时全严格正，$\eta=1$ 时前三项为零仍合法。全部函数都可积，且

$$
C(S_0)=(2,2,2)=C(S_\eta),\qquad \int s_i h\,d\lambda=-1+1=0.
$$

现在供应只通过第四波段的被动滤光器 $a=\mathbf1_{B_4}$。则

$$
aS_0=\mathbf1_{B_4},\qquad
aS_\eta=(1+\eta)\mathbf1_{B_4},
$$

从而

$$
C(aS_0)=(1,1,1),\qquad
C(aS_\eta)=(1+\eta,1+\eta,1+\eta),
\qquad \Delta C'=\eta(1,1,1)\ne0.
$$

**证明。** 每个 $s_i$ 在一个前波段和第四波段上取一，因此初始读数分别为 $1+1=2$ 和 $(1-\eta)+(1+\eta)=2$。滤光后只剩第四波段，故读数是该波段的值乘以一的测度。透射率只取零、一，符合被动条件；两个源的积分分别为 $4$ 与 $4-2\eta$，输出积分分别为 $1$ 与 $1+\eta$，都不超过各自输入。没有负光谱、负透射或增益。$\square$

这是声明的分段常数三路传感器模型，不是采用实测 CIE 匹配曲线的数值实例，也不以该构造宣称某一现实颜色对已经实现。$\eta=0$ 时两源相同且返回为零；使用常数滤光器时，即使 $\eta>0$ 也仍同读数。与量子例子相同，取得末端差异需要实际可调用的后续操作与相应读数。

### 8.11. 相同读出结构的对应与预测摘要的边界

**定义 8.33（共同的纤维返回结构）。** 对观察映射 $\mathcal O$ 与共同合法的操作 $T$，当前观察能够唯一预测该操作后的同组观察，精确地要求 $\mathcal O\circ T$ 在 $\mathcal O$ 的每条实际纤维上恒定。以上例子的参数对应是：

| 来源对象与当前区别 | 当前合并条件 | 指定操作后的读数差 |
| --- | --- | --- |
| 五模式密度矩阵差 $\delta\rho$ | $\operatorname{Tr}(A\delta\rho)=0$，$A\in\mathcal W$ | $\operatorname{Tr}(U^\dagger AU\,\delta\rho)$ |
| 两量子位联合态差 $\delta\rho_{AB}$ | 给定局部部分迹相同 | 指定联合效果的期望差 |
| 合法光谱差 $h$ | $\int s_i h=0$ | $\int s_i a h$ |

五模式相位族在 $U_\theta$ 下留在当前概率纤维内，而非盲 $R_1(\alpha)$ 的残差可使其中某些区别返回占位读数；Bell 相位族留在相同局部态纤维内，而已供应的联合相关读口能区分相位；光谱核方向在当前三路下被合并，而所供滤光器可使其返回。三者对应的是观察纤维及其与操作的相容性，不是三种来源空间的同构。空间三坐标、颜色三刺激值和量子位三 Pauli 期望的定义域、合法域及可操作资源各自不同；共有三个实数不能识别这些载体，更不能由此推出同一种物理动力学。

**推论 8.34（任务所需的摘要细化）。** 若指定任务必须准确预测一个菜单中的全部允许未来读数，而当前摘要有上述同当前、异未来的合法状态对，则任何完成此任务的摘要都必须区分这一对，或者已经包含能区分它们的历史信息。

**证明。** 假设某个摘要仍把该对合并。只依赖此摘要的预测器对两态给相同答案，但该合法未来任务的正确答案不同，因此不可能同时正确。$\square$

在五模式模型中，当前统计稳定、$\zeta$ 演化与后续返回读数可以同时成立；是否需要新增关系信息，由实际任务和菜单决定。闭合菜单下无需为这些末端均值再增加被永远合并的区别；非闭合菜单下，仅后处理旧摘要无法消除已给出的反例。这里所需的细化是预测任务中的区分能力，不自动意味着新增物理空间维数、无限记忆、可认证的全部状态或额外控制资源。关于完整仪器历史的细化，使用 [B]、[C] 已有的逐输出词效果闭包，不能以末端均值闭合替代。

### 8.12. 数学来源与适用范围

[B79]: https://github.com/the-omega-institute/trureturing/blob/79c480111cfceca83f9c2f191117ecd21d74431d/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md
[L]: https://github.com/the-omega-institute/trureturing/blob/79c480111cfceca83f9c2f191117ecd21d74431d/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md
[C]: https://github.com/the-omega-institute/trureturing/blob/79c480111cfceca83f9c2f191117ecd21d74431d/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md
[IBM]: https://quantum.cloud.ibm.com/learning/en/courses/general-formulation-of-quantum-information/density-matrices/bloch-sphere
[CIE]: https://cie.co.at/eilvterm/17-23-008

[B] 《AURIC FIB 关系丛与预测闭包理论》，[固定源正文](https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)。定理 3.2–3.3 供应唯一五点展开、占位纤维与宽度；定理 4.2 供应非零图上的 $\zeta=e^{\tau/2-i\chi}$；定理 7.3 供应核保持下降；定义 8.1、8.3 与定理 8.4 供应有限维仪器及逐输出未来效果闭包；命题 8.9–8.10 供应有条件的合法端点与联合相位接口；命题 10.3–10.4 供应概率不变的关系相位门与闭包残差。本文取该卷的模式次序、正相位变量约定和不归一化迹内积，明确消费这些中间结构。

[B79] 《AURIC FIB 关系丛与预测闭包理论》，定理 8.4、命题 8.9–8.10、10.3 及 §18.1–18.2：有限维逐分支闭包、有条件的端点与相位控制，以及图关系系数的对角统计和相位接口。相位保持概率并不蕴含菜单闭合；具体未来返回由本节的端点响应和拉回残差计算承担。

[O] 《观察者相对的 Auric FIB–ATOM：局部模型、接口与未来可辨识性》，[固定源正文](https://github.com/the-omega-institute/trureturing/blob/04dfb26329ca7ab2c9d3488f461fa376000e171f/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md)，定义 4.1–4.2、命题 4.3。使用其输入模式及三均值与完整联合记录的区别；其读出次序 $(X,Z,Y)$ 在本文改排为 $(X,Y,Z)$，概率分量次序不变。

[L] 《AURIC FIB 观察者内部三轴几何与预测接口》，[固定源正文](https://github.com/the-omega-institute/trureturing/blob/79c480111cfceca83f9c2f191117ecd21d74431d/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)，定义 9.1、9.3。前者供应固定 Pauli/Bloch 载体、合法球及取得条件，后者供应同一保留环境上的联合区别返回；它们不识别几何位置空间与局部算符空间。

[C] 《Auric FIB ATOM：静态隐藏纤维、输出分辨未来商与可维护性》，[固定源正文](https://github.com/the-omega-institute/trureturing/blob/79c480111cfceca83f9c2f191117ecd21d74431d/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)，§§15–16 及其适用条件。消费逐输出子核闭包和平均转移闭合不足以预测完整记录的区别；本文量子仪器的定义与证明采用 [B] 的完全正映射版本。

[IBM] IBM Quantum Learning, [“Bloch sphere”](https://quantum.cloud.ibm.com/learning/en/courses/general-formulation-of-quantum-information/density-matrices/bloch-sphere)，General formulation of quantum information，Density matrices。该原始教学来源给出 Pauli 展开、纯态球与含混态的 Bloch 球体；本文的唯一性与正性计算按固定二维载体直接列出。

[CIE] CIE, International Lighting Vocabulary, [17-23-008, “metameric colour stimuli”](https://cie.co.at/eilvterm/17-23-008)。采用其“指定色度系统中三刺激值相同而光谱不同”的定义；四波段例子另行明确其传感函数，未把它们当作实测标准观察者曲线。

## 追加锚（本行以下为增补区）

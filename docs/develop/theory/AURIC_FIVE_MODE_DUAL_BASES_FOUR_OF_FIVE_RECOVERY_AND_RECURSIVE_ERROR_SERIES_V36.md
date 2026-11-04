# AURIC：五模式双基、四推一与递归误差级数

从完整关系基到条件恢复、锐稳定界与收敛尾部

定义、定理与纸面证明　v36.0  
2026 年 10 月 31 日　Asia/Singapore

原稿 PDF 元数据：作者 AURIC research continuation；主题 Five-mode observable algebra, conditional erasure recovery, sharp relation stability and convergent recursive error。

> **编校说明（非原稿正文）**：以下保留作者原稿的完整论述。文中“本轮”“当前”“新增”、读取范围、合并记录及未执行验证等表述，均属于作者写作时的历史陈述；不表示本 Markdown 转换已重做相应历史审计、形式验证或实际取得协议。第 10 节的测度族措辞另附局部编校注，原句保留。

## 摘要

本稿回应“三轴、关系、归一化是否构成任意四推一的五模式语义，以及结果与误差是否递归形成级数”。
项目原五模式函数代数确有完整基 $\{1,x,y,z,xy\}$：常数一、三个占据轴和一个联合关系。
这五个基元线性独立；归一化状态上的五事件概率则满足总和一，允许已知位置的单项擦除恢复。
本文区分这两个基，并证明：对同尺度未归一矩 $(N,X,Y,Z,K)$，若另固定正交叉比
$\vartheta$，则 $(N-X-Y-Z+K)K=\vartheta(X-K)(Y-K)$ 对任意缺失坐标都可唯一求解。
给出统一支撑裕量下的稳定常数；在同三轴纤维上进一步证明锐界
$\operatorname{TV}(p,\tilde p)\le(1-Z)\tanh(|\chi-\tilde\chi|/8)$。
结果与误差的正关系矩阵给精确相对残差式，但相消边界会放大恢复误差。
随后以四角闭合、正交精化、收缩残差方程和归一历史混合建立递归级数的严格版本，
并给非均匀收缩率与实际注入误差的充分条件。
最后接入本轮新增的范数紧误差族统一有限读出结果，说明误差仍须实际可检测。
全部构造解释为同一静态整体内部的读出与记录关系；不由五个名称、归一化或酉性单独推出普遍纠错。

<a id="section-1"></a>

## 1　固定来源与本轮问题的准确分层

本轮固定 `dev` 提交为

`38076d7a280e0e8186c3d5507e3dea59b6d4803c`，

提交时间为 2026-10-31 03:23:01（新加坡），比较基线为 v35 的

`64369c37c781a34e67281ba38b315dc31fdf9115`。
直接供应是基础公式卷 §§2、4、6–9、12.5、14，以及
`FiveModeMixedCoordinates`。

本次新增的相关接口是
`FiniteObservationVariation` 对范数紧误差族的统一有限读出扩展。
五函数基、最大熵补全、混合坐标和四角闭合均属既有来源；本稿给出其新的组合应用与纸面推论。
来源读取不等于执行形式验证，本轮未运行 Lean、CAS、数学数值求值或候选枚举。[1](#bib-head)、[2](#bib-foundation)、[3](#bib-mixed)、[4](#bib-finiteobs)

继续固定单一静态整体 $(\mathcal A,\omega)$；观察者、误差、准备、计算、记录和内部索引均在其中。
下文的概率律、Hilbert 分解、通道与张量因子是已声明的内部接口表示。
复 Hilbert、Born 读出及 CPTP 结构都是附加接口前件，不由五函数代数单独推出。
原五函数代数描述同一个有限窗口上的经典模式函数，不自动代表全部非对易量子观察量。
本稿不把存在性证明改写为实际取得协议。

距离约定为 $\operatorname{TV}(p,q)=\tfrac12\|p-q\|_1$、
$D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$。
对同一有限载体上的通道，令

$$
d_{\rm ref}(\Phi,\Psi)=\sup_{R,\rho}
D\bigl((\Phi\otimes\operatorname{id}_R)(\rho),(\Psi\otimes\operatorname{id}_R)(\rho)\bigr),
$$

上确界遍及有限维内部参考角色 $R$ 及其与载体的归一联合态。
有符号测度的总变差范数另记为 $\|s\|_{\rm var}$，不含上述二分之一因子。

“五项”至少有三种不同类型：五个事件概率，五个可观测函数基元，五个受额外关系限制的矩坐标。
要证明任意四推一，必须说明是哪一类、已知哪些侧条件，以及缺失位置是否已知。
本稿的正面结论是：**五模式确有“三轴加联合关系加常数一”的完整语义；四推一则是声明约束后的恢复性质。递归能够形成收敛级数，还需要闭合与尾部控制。**

<a id="section-2"></a>

## 2　五模式的两个完整基：事件与语义矩

<a id="def-2-1"></a>

### 定义 2.1（原五模式函数域）

令 $\Sigma=\{0,2,3,5,25\}$，占据函数 $x,y,z$ 在五模式上的值为

$$
\begin{array}{c|ccccc}
s&0&2&3&5&25\\\hline
(x,y,z)&(0,0,0)&(1,0,0)&(0,0,1)&(0,1,0)&(1,1,0).
\end{array}
$$

故 $x^2=x,y^2=y,z^2=z,xz=yz=0$，而 $xy$ 可以非零。

<a id="thm:basis"></a>

### 定理 2.2（五函数基与五事件基）

有限函数代数有表示

$$
\mathbb R^\Sigma\simeq
\mathbb R[x,y,z]/(x^2-x,y^2-y,z^2-z,xz,yz),
$$

且 $\{1,x,y,z,xy\}$ 是一组基。五个事件指示函数为

$$
\begin{aligned}
e_0&=1-x-y-z+xy,&e_2&=x-xy,&e_3&=z,\\
e_5&=y-xy,&e_{25}&=xy,
\end{aligned}
$$

满足 $e_se_t=\delta_{st}e_s$、$\sum_se_s=1$。

**证明。**

幂等关系将所有单项式指数降至零或一；含 $xz$ 或 $yz$ 的单项式消失，余下仅为
$1,x,y,z,xy$。若其线性组合在全部模式上为零，依次在 $0,2,5,3$ 评价，得到前四个系数为零，
再在 $25$ 评价得到最后系数为零。因此余类独立且张成，评价给所述代数同构。
逐点代入五个 $e_s$，各自恰在一个模式上为一，其余为零，即得事件关系。

∎

这就是用户所说五项语义在项目中的直接代数对应；该结果已有基础公式卷 §2.2 的完整证明。
尤其 $e_0\ne1$：实际空窗事件与对全部模式成立的常数一有不同含义。[2](#bib-foundation)

<a id="def-2-3"></a>

### 定义 2.3（同尺度的五个未归一语义矩）

给严格正模式质量 $w_s>0$，定义

$$
N=\sum_sw_s,\quad X=w_2+w_{25},\quad Y=w_5+w_{25},\quad
Z=w_3,\quad K=w_{25}.
$$

本稿大写 $X,Y,Z,K$ 在本节及下一节均为*未归一矩*，与 $N$ 同尺度。
$N=1$ 时恢复项目通常的归一坐标。

<a id="thm:moments"></a>

### 定理 2.4（双基变换及独立性）

质量向量与五矩 $\mu=(N,X,Y,Z,K)$ 线性一一对应，逆式为

$$
\boxed{w=(N-X-Y-Z+K,\ X-K,\ Z,\ Y-K,\ K).}
$$

其严格正域是 $\mathbb R^5$ 中的开凸锥。
在没有额外条件时，删除五矩中的任一项，都不能唯一恢复该项。

**证明。**

把矩定义逐项解回即得逆式，故变换可逆；五个严格正线性不等式给开凸锥。
在任意内部点，可只将某一个矩坐标改变充分小的正负量，其余四项固定，仍留在开锥。
于是被删除项至少有两个相容值。

∎

归一化 $N=1$ 将自由度降为四；此时完整状态由 $(X,Y,Z,K)$ 决定。
也可以用隐藏关系

$$
\chi=\log\frac{w_0w_{25}}{w_2w_5}
$$

替换 $K$。项目 `mixed_coordinates_global_chart` 证明，
每个内部三轴点与每个 $\chi\in\mathbb R$ 恰对应一个严格正归一律。
所以归一的 $(X,Y,Z,\chi)$ 仍是四个独立坐标。[3](#bib-mixed)

金字塔底面的仿射关系为 $v_0+v_{25}=v_2+v_5$，其隐藏方向为
$(1,-1,0,-1,1)$；法向模式 $3$ 的系数为零。
这个四角回路也不是对全部五个顶点都非退化的五元约束。

<a id="section-3"></a>

## 3　四推一：精确恢复、稳定恢复与额外关系

<a id="def-3-1"></a>

### 定义 3.1（已知位置的单项恢复）

令 $\mathcal M\subseteq Y_1\times\cdots\times Y_5$ 为实际相容五元组的集合。
称第 $i$ 项可由其余四项恢复，若存在映射 $D_i$，使
$D_i(\pi_{-i}m)=m_i$ 对全部 $m\in\mathcal M$ 成立。

<a id="prop:erasure"></a>

### 命题 3.2（恢复的核判据与事件概率情形）

第 $i$ 项可恢复，当且仅当 $\pi_{-i}$ 在 $\mathcal M$ 上单射。
对已知总量 $N$ 的五个模式质量，任意四项都给

$$
w_i=N-\sum_{j\ne i}w_j.
$$

若每个已读质量误差至多为 $\epsilon$、$N$ 精确，则缺失项误差至多为 $4\epsilon$。

**证明。**

解码存在时，同一四元读出必有相同第五项；反之，单射性使解码在实际像上良定义。
质量公式来自总和约束，误差界来自四项三角不等式。

∎

这里归一总量是已知侧条件。对于语义矩五元组，其中的 $N$ 已占一个位置；
不能重复把它同时算作一个未知自由坐标与一条额外已知关系。
Bloch 球面亦显示“有一个方程”不足以保证全局恢复：给两个分量，第三分量仍可能有正负分支，
而在某分量趋零处，选定平方根分支的逆映射也可能病态。

<a id="prop:correction"></a>

### 命题 3.3（一次擦除恢复并不等于一次未知错误纠正）

单个总和约束能恢复已知位置的缺失质量，但一般不能确定哪个读数发生了错误。

**证明。**

取严格正归一 $p$、不同坐标 $i,j$ 和充分小 $\delta>0$，令
$q=p+\delta e_i-\delta e_j$。二者都是合法律。
观测向量 $y=p+\delta e_i=q+\delta e_j$，既可由 $p$ 的第 $i$ 项损坏得到，
也可由 $q$ 的第 $j$ 项损坏得到。总和偏差可以被检测，却不能唯一定位错误。
此外，总和为零的双坐标误差甚至保持归一化。

∎

<a id="thm:fourfive"></a>

### 定理 3.4（固定正交叉比下的语义矩四推一）

在定理 [2.4](#thm:moments) 的严格正域内，另固定一个已知参数 $\vartheta>0$，要求

$$
\frac{w_0w_{25}}{w_2w_5}=\vartheta.
$$

则相容语义矩满足

$$
\boxed{F_\vartheta(\mu):=(N-X-Y-Z+K)K-\vartheta(X-K)(Y-K)=0.}
$$

在该相容类上，任意四个*同尺度未归一矩*唯一决定第五个。
当 $\vartheta=1$ 时，关系简化为

$$
\boxed{(N-Z)K=XY.}
$$

**证明。**

代入双基逆式即得 $F_\vartheta=0$。在严格正域内，各坐标偏导为

$$
\begin{aligned}
F_N&=K>0,&F_Z&=-K<0,\\
F_X&=-[K+\vartheta(Y-K)]<0,&
F_Y&=-[K+\vartheta(X-K)]<0,\\
F_K&=w_0+K+\vartheta(w_2+w_5)>0.
\end{aligned}
$$

若两个相容点仅一个坐标不同，连接它们的线段仍在严格正开锥；
$F_\vartheta$ 沿该线段严格单调，不能两端都为零，故删除任意坐标均为单射。
存在性只在实际相容的四项数据上要求，不宣称任意四个数都有合法补全。
$\vartheta=1$ 时展开并约去 $K^2$，得 $(N-Z)K=XY$。

∎

特别在 $\vartheta=1$ 的严格正域，五个解码公式为

$$
\begin{gathered}
K=\frac{XY}{N-Z},\qquad
X=\frac{(N-Z)K}{Y},\qquad
Y=\frac{(N-Z)K}{X},\\
N=Z+\frac{XY}{K},\qquad
Z=N-\frac{XY}{K}.
\end{gathered}
$$

该特例是底面条件独立的乘积补全；项目已有完整来源与适用范围。
固定 $\vartheta$ 是额外关系前件，不能由一般五模式归一化推出。[2](#bib-foundation)、[3](#bib-mixed)

<a id="thm:fourfivebound"></a>

### 定理 3.5（四推一的统一误差界）

固定 $\vartheta$，设两份相容数据均满足每个模式质量 $w_s\ge\eta>0$、总量 $N\le M$。
则对任意缺失项 $i$，

$$
\boxed{|\mu_i-\tilde\mu_i|
\le\frac{\max(1,\vartheta)M}{\eta}
\sum_{j\ne i}|\mu_j-\tilde\mu_j|.}
$$

**证明。**

两点间的线段仍满足相同质量裕量与总量上界，虽然线段未必在 $F_\vartheta=0$ 上。
沿线段积分梯度得
$0=\sum_jA_j(\mu_j-\tilde\mu_j)$，其中 $A_j$ 为该偏导的线段平均。
各偏导符号固定，故 $|A_i|\ge\eta$；所列偏导又给
$|A_j|\le\max(1,\vartheta)M$。解出第 $i$ 项并取绝对值即可。

∎

特别的 $K$ 解码更稳定。令 $D=F_K$，隐微分给

$$
K_N=-K/D,\quad K_Z=K/D,\quad
K_X=[K+\vartheta(Y-K)]/D,\quad
K_Y=[K+\vartheta(X-K)]/D.
$$

各绝对值均小于一。固定 $\vartheta$ 的凸可见域为
$X,Y,Z>0$、$X+Z<N$、$Y+Z<N$；每点的相容 $K$ 存在性由混合坐标定理经总量缩放得到。
因此在该域内，
$|\Delta K|\le|\Delta N|+|\Delta X|+|\Delta Y|+|\Delta Z|$，无需共同支撑裕量。
但恢复其他坐标可能病态，例如 $\vartheta=1$ 时 $\partial X/\partial K=(N-Z)/Y$ 可无界。

**尺度范围不可省略。** 若先改用 $\bar X=X/N,\bar Y=Y/N,\bar Z=Z/N,\bar K=K/N$，
交叉比方程变为

$$
(1-\bar X-\bar Y-\bar Z+\bar K)\bar K
=\vartheta(\bar X-\bar K)(\bar Y-\bar K),
$$

它完全不含 $N$。因此四个归一比值不能恢复原总量；定理 [3.4](#thm:fourfive) 的五项必须同尺度。

<a id="section-4"></a>

## 4　关系读数怎样控制完整五模式误差

本节固定 $N=1$，记 $w=1-Z$。给内部三轴 $X,Y,Z>0$、$X+Z<1$、$Y+Z<1$，
以 $k=p_{25}$ 参数化同三轴纤维：

$$
p(k)=(w-X-Y+k,\ X-k,\ Z,\ Y-k,\ k),
\quad L<k<U,
$$

其中 $L=\max(0,X+Y-w)$、$U=\min(X,Y)$。定义自然对数关系

$$
\chi(k)=\log\frac{(w-X-Y+k)k}{(X-k)(Y-k)}.
$$

<a id="thm:chi"></a>

### 定理 4.1（关系坐标的唯一性与初步稳定界）

$\chi:(L,U)\to\mathbb R$ 为严格递增双射，且

$$
\chi'(k)=\frac1{p_0}+\frac1{p_{25}}+\frac1{p_2}+\frac1{p_5}
\ge\frac{16}{w}.
$$

故同三轴两律满足

$$
|k-\tilde k|\le\frac w{16}|\chi-\tilde\chi|,
\qquad
\operatorname{TV}(p,\tilde p)=2|k-\tilde k|
\le\frac w8|\chi-\tilde\chi|.
$$

**证明。**

求导得所列正导数；四个底面概率之和为 $w$，Cauchy–Schwarz 给倒数和至少为 $16/w$。
在下端点，分子至少一项趋零而分母为正；在上端点，分母至少一项趋零而分子为正。
故两端极限分别为负、正无穷，连续性与单调性给双射。
积分导数下界给 $k$ 界；两律之差为 $(k-\tilde k)(1,-1,0,-1,1)$，得 TV 等式。

∎

双射及隐藏方向的 Fisher 导数关系由项目混合坐标源已有证明。
下面的锐两点估计是本稿对该供应的定量应用。[3](#bib-mixed)

<a id="thm:sharp"></a>

### 定理 4.2（隐藏关系误差的锐两点界）

在同一个内部三轴点上，

$$
\boxed{\operatorname{TV}(p,\tilde p)
\le w\tanh\!\left(\frac{|\chi-\tilde\chi|}{8}\right).}
$$

该界对全部内部三轴与关系值统一，且可达到。

**证明。**

不妨 $\tilde k-k=h>0$，取四个正数

$$
(a_1,a_2,a_3,a_4)
=(p_0(k),p_{25}(k),p_2(\tilde k),p_5(\tilde k)).
$$

它们的和为 $w-2h>0$，且

$$
\tilde\chi-\chi=\sum_{i=1}^4\log(1+h/a_i).
$$

函数 $f_h(a)=\log(1+h/a)$ 的二阶导数为
$h(2a+h)/(a^2(a+h)^2)>0$，所以 Jensen 不等式给

$$
\tilde\chi-\chi
\ge4\log\frac{w+2h}{w-2h}
=8\operatorname{artanh}\frac{2h}{w}.
$$

反解且使用 $\operatorname{TV}=2h$ 即得。
当 $X=Y=w/2$、两关系值互为相反数时，可以让上述四个 $a_i$ 全相等，
从而达到 Jensen 等号。对任意有限关系差均可如此构造严格正律。

∎

<a id="prop:entropy"></a>

### 命题 4.3（最大熵截面与相对于它的锐关系界）

在固定三轴的纤维上，唯一最大 Shannon 熵律满足 $\chi=0$，即

$$
k_*=\frac{XY}{w}.
$$

其余同三轴正律满足

$$
\boxed{\operatorname{TV}(p,p_*)\le\frac w2\tanh\!\left(\frac{|\chi|}{4}\right).}
$$

**证明。**

这里采用自然对数熵 $H(p)=-\sum_sp_s\log p_s$。
纤维上 $H'=-\chi$、$H''=-\chi'<0$，因此唯一最大点为 $\chi=0$。
交叉乘积等式化简为 $wk_*=XY$。
将四格除以 $w$，记为 $a,b,c,d$，其和为一；令 $u=\sqrt{ad}$、$v=\sqrt{bc}$。
AM–GM 给 $u+v\le1/2$，而 $u/v=e^{\chi/2}$，故

$$
|ad-bc|=(u+v)|u-v|
\le\frac14\tanh(|\chi|/4).
$$

又有 $k-k_*=w(ad-bc)$，结合 TV 等式即可。
$X=Y=w/2$ 且 $a=d,b=c$ 时达到此界。

∎

最大熵补全在项目基础公式卷 §9.3 已对整个闭单纯形证明，本稿只重述内域的微分证明，
新增的是对关系偏离的上述锐估计。最大熵选择是一种明确的补全规则，未证明实际来源就处在该截面。
它还通常非线性：固定 $w$，边缘分别为 $X=Y=w/4$ 和 $X=Y=3w/4$ 的两份独立表，
平均联合量为 $5w/16$，而平均边缘的独立表联合量为 $w/4$。
所以不能自动把该补全当成一个固定随机矩阵或 CPTP 通道。[2](#bib-foundation)

这些界的对象是完整五模式概率律。对任意目标函数 $f$，源中的展开给

$$
\mathbb E_p f-\mathbb E_{\tilde p}f
=J_f(k-\tilde k),\qquad J_f=f_{25}-f_2-f_5+f_0.
$$

因此关系误差也直接控制所有指定窗口目标；取得精确或近似 $\chi$ 仍需实际读出合同。
从概率噪声反推对数关系时，零概率附近的敏感性并没有被这些逆向界消除。

<a id="section-5"></a>

## 5　递归首先要求读出与更新闭合

<a id="def-5-1"></a>

### 定义 5.1（同一个五态更新合同）

另行给定列随机矩阵 $T$，$T_{ts}\ge0$、$\sum_tT_{ts}=1$，作用于归一模式律为 $p'=Tp$，
并线性延拓至非负有限质量。
若 $L$ 是定理 [2.4](#thm:moments) 的线性矩变换，则五矩更新为

$$
\mu'=LTL^{-1}\mu.
$$

这是原源文件行向量约定 $p'=pT$ 的转置记法。

<a id="thm:closure"></a>

### 定理 5.2（三均值递归的四角闭合判据）

令 $v_s=(x(s),y(s),z(s))$、$\Phi_s=\sum_tT_{ts}v_t$。
下一三均值对所有输入只依赖当前三均值，当且仅当

$$
\boxed{\Phi_0+\Phi_{25}=\Phi_2+\Phi_5.}
$$

**证明。**

两份同三均值律的差为 $h(1,-1,0,-1,1)$，下一均值差恰为
$h(\Phi_0-\Phi_2-\Phi_5+\Phi_{25})$。
该括号为零时充分；若非零，取内部纤维中不同的两个 $h$ 即反驳唯一预测。

∎

这是基础公式卷 §14.5 已有的精确条件。五个完整矩可以承载声明的有限核更新，
三个可见矩却需要该闭合。一般原生历史是否自治于同一个五态载体，仍是独立前件。[2](#bib-foundation)

四推一递归也有相同要求。若 $\mathcal M_\vartheta=\{F_\vartheta=0,w_s>0\}$，
某个删除映射 $C$ 在其上有逆 $D$，而矩更新 $B=LTL^{-1}$ 保持
$B\mathcal M_\vartheta\subseteq\mathcal M_\vartheta$，
则压缩更新 $g=CBD$ 满足 $g^nC=CB^n$，由归纳直接证明。
若更新破坏固定交叉比，便需要追踪新的关系参数或扩大状态；当前可恢复不自动成为下一层可恢复。

<a id="prop:branches"></a>

### 命题 5.3（记录条件化需要未归一的联合更新）

设动作 $a$、回复 $b$ 的分支矩阵为 $M_{a,b}\ge0$，并满足
$\sum_b\mathbf1^TM_{a,b}=\mathbf1^T$。
定义每个纯模式上的回复质量与未归一下一三矩

$$
\ell_{a,b}(s)=\mathbf1^TM_{a,b}e_s,\qquad
\gamma_{a,b}(s)=\sum_t(M_{a,b})_{ts}v_t.
$$

若对每个 $a,b$，两者均满足四角等式，则当前三均值确定该回复概率，
并在其为正时确定回复后的三均值。相同合同可递归预测全部有限适应性联合回复。

**证明。**

回复概率为 $m_b=\sum_sp_s\ell_{a,b}(s)$，未归一下一矩为
$u_b=\sum_sp_s\gamma_{a,b}(s)$。四角条件使二者均由当前三均值确定。
$m_b>0$ 时更新为 $u_b/m_b$；质量零时不定义该条件态。
对每个实际发生的回复历史应用同一更新，逐层相乘条件概率即得联合律。
反馈动作由已取得历史决定，因此不破坏这项归纳。

∎

只检查无条件回复边缘与无条件下一均值不够，源 §14.6 有明确二步反例。
若全部事件包括拒绝或失败，归一化必须在完整结果上进行；不能静默删除分支质量。
五模式当前律也不能自动恢复量子相位、来源括号或将来重新接入的内部记忆。

<a id="section-6"></a>

## 6　结果与误差组成新的正关系，但尺度仍须保留

在一个固定相位约定的复 Hilbert 表示或一般 Hilbert 近似问题中，设

$$
\psi=x+e,\qquad\psi\ne0.
$$

$x$ 为当前结果，$e$ 为残差；本节不把任意密度矩阵差当成正态。
取内积对第一变量共轭线性，定义

$$
p=\|x\|^2,\quad q=\|e\|^2,\quad c=\langle e,x\rangle,\quad S=p+q,
\qquad G=\begin{pmatrix}p&\bar c\\c&q\end{pmatrix}\ge0.
$$

由 Cauchy–Schwarz，$|c|^2\le pq$。沿用 v35 的归一坐标

$$
r_x=2\Re c/S,\qquad r_y=2\Im c/S,\qquad r_z=(p-q)/S,
$$

得到 $|\mathbf r|\le1$。
这些是二元结果–误差 Gram 关系的坐标；它们与原五模式的三个占据函数具有不同的定义，
只有另给明确映射后才能识别为同一读出接口。

<a id="thm:gramerror"></a>

### 定理 6.1（结果、误差与目标归一化的精确关系）

上述分解满足

$$
\boxed{\|\psi\|^2=S(1+r_x),\qquad
\frac{\|e\|^2}{\|\psi\|^2}=\frac{1-r_z}{2(1+r_x)}.}
$$

若两份数据均有 $1+r_x\ge\gamma>0$，则相对误差平方函数
$f(\mathbf r)=(1-r_z)/(2(1+r_x))$ 满足

$$
|f(\mathbf r)-f(\tilde{\mathbf r})|
\le\frac{|r_z-\tilde r_z|}{2\gamma}
   +\frac{|r_x-\tilde r_x|}{\gamma^2}.
$$

**证明。**

展开目标范数给 $\|x+e\|^2=p+q+2\Re c=S(1+r_x)$，且
$q=S(1-r_z)/2$。目标非零保证分母为正，相除即得公式。
对稳定界先改变分子，再改变分母，使用 $1-\tilde r_z\le2$ 和两个分母的共同下界。

∎

这个公式给“结果与误差也有关系且可以归一化”一个严格版本，但没有说任意五项均可互换恢复：
目标范数约束未单独固定 $r_y$，也未单独固定 $r_z$。
此外，真实目标和关系读数是否可取得，须与形式分解分开。

<a id="prop:cancel"></a>

### 命题 6.2（稳定的归一方向可以隐藏无界相消误差）

取单位向量 $u$、$M>1$，令 $x=Mu$、$e=(1-M)u$。
则目标恒为 $\psi=u$，但 $\|e\|=M-1\to\infty$，而归一三轴趋于固定点 $(-1,0,0)$。

**证明。**

$S=M^2+(M-1)^2$，直接得到
$r_x=-1+1/S$、$r_y=0$、$r_z=(2M-1)/S$。
因此三轴收敛，而误差尺度无界；恰是 $1+r_x\downarrow0$ 造成恢复病态。

∎

反方向也有区别：$e_n=2^{-n}u_n$，若单位向量 $u_n$ 在两个正交方向间交替，
则真实误差范数趋零，而归一误差方向不收敛。
因此应该控制带尺度的误差，而不必把归一方向收敛当成所有任务的必要条件。

<a id="prop:signederror"></a>

### 命题 6.3（有符号误差的归一化要保留符号与质量）

若 $p,\tilde p$ 为归一模式律，$\delta=\tilde p-p\ne0$，则 $\sum_s\delta_s=0$，
不能用该总和把误差归一化。令 $\delta_+,\delta_-$ 为逐项正负部分，
$\epsilon=\operatorname{TV}(p,\tilde p)$，则

$$
\sum_s(\delta_+)_s=\sum_s(\delta_-)_s=\epsilon,\qquad
\delta=\epsilon(q_+-q_-),\quad q_\pm=\delta_\pm/\epsilon.
$$

其中 $q_+,q_-$ 是支撑不交的概率律。若需一个正的归一记录，可在内部符号标签上取

$$
\mathfrak e(s,\pm)=\frac{(\delta_\pm)_s}{2\epsilon},\qquad
\sum_{s,\pm}\mathfrak e(s,\pm)=1.
$$

仍须另保留尺度 $\epsilon$；仅记录 $\mathfrak e$ 会丢失误差大小。

**证明。**

零总质量给正负质量相等，它们的和为 $\|\delta\|_1=2\epsilon$。
逐项归一化即得各式。若 $\delta=0$，无需定义误差方向，直接记录零尺度即可。

∎

对于有限维密度矩阵差，同一论证应用于自伴正负谱部分。
因此“误差也可归一化”可以严格实现，但误差的类型、符号记录和尺度不能省略；
没有额外可压缩结构时，该记录也不自动缩成原三轴或单个五模式律。

<a id="prop:derivederror"></a>

### 命题 6.4（误差继承的是依赖当前结果的派生关系）

记 $\mu$ 为当前五矩，$\delta$ 为目标五矩减去当前五矩。
若目标满足 $F_\vartheta(\mu+\delta)=0$，则精确地

$$
\boxed{F_\vartheta(\mu)+DF_\vartheta(\mu)[\delta]
       +F_\vartheta(\delta)=0.}
$$

即使当前结果也满足 $F_\vartheta(\mu)=0$，误差一般仍不满足 $F_\vartheta(\delta)=0$。

**证明。**

$F_\vartheta$ 是齐次二次多项式，所以二次 Taylor 展开精确终止，给出等式。
例如 $\vartheta=1$、$W=N-Z>0$，在某内部相容点保持 $N,Z$ 不变，
将 $X,Y$ 各增加充分小的同一个 $h\ne0$，则相容 $K$ 的变化为
$\delta K=h(X+Y+h)/W$。
于是 $\delta=(0,h,h,0,\delta K)$，但 $F_1(\delta)=-h^2\ne0$。

∎

因此结果、误差和约束确有新的精确关系；若要层层重复同一个误差模型，必须证明该派生关系闭合。
在相容基点上沿约束面作无穷小扰动，其切向量 $v$ 满足 $DF_\vartheta(\mu)[v]=0$；
有限误差则要保留二次项。

<a id="cor:decoderseries"></a>

### 推论 6.5（四推一解码的分母扰动本身生成几何级数）

在 $\vartheta=1$ 时，令 $W=N-Z>0$，缺失项为 $K=XY/W$。
对扰动后的相容读数 $X',Y',W'=W+\Delta W$，若
$r=|\Delta W|/W<1$，则

$$
K'=\frac{X'Y'}{W'}
=\frac{X'Y'}{W}\sum_{j=0}^{\infty}
  \left(-\frac{\Delta W}{W}\right)^j.
$$

取前 $m\ge1$ 项的近似为 $K'_m$，则

$$
\boxed{|K'-K'_m|\le\frac{|X'Y'|}{W}\frac{r^m}{1-r}.}
$$

**证明。**

从 $1/W'=W^{-1}(1+\Delta W/W)^{-1}$ 应用绝对收敛的几何级数，
再对其尾部逐项估计即可。目标误差 $K'-K$ 由该级数减去原值 $K$ 得到。

∎

这个级数直接来自五模式四推一的归一分母，而非仅仅是递归的类比。
把误差自身写出来也很明确：令 $\Delta K=K'-K$，$\alpha=-\Delta W/W$，并令

$$
r_0=\frac{X\Delta Y+Y\Delta X+\Delta X\Delta Y-K\Delta W}{W}.
$$

两份关系相减给 $\Delta K=r_0+\alpha\Delta K$，所以在 $|\alpha|<1$ 时

$$
\Delta K=\sum_{j\ge0}\alpha^j r_0,\qquad
\left|\Delta K-\sum_{j<m}\alpha^j r_0\right|
\le\frac{|r_0|\,|\alpha|^m}{1-|\alpha|}.
$$

此处 $r_0$ 只依赖原值和四个已读坐标的扰动，不含待恢复的 $\Delta K$；
扰动读数或其证书的实际取得仍为前件。
分母裕量不足时，形式展开不保证收敛；这与前述逆映射条件数恶化是同一边界现象。

<a id="section-7"></a>

## 7　递归确实可以成为级数：正交精化与关系残差

<a id="thm:orthogonal"></a>

### 定理 7.1（静态目标的正交精化与精确尾式）

设 $P_n$ 是同一 Hilbert 空间上的递增正交投影，$P_n\le P_{n+1}$。
对固定目标 $\psi$，定义

$$
x_n=P_n\psi,\quad e_n=(I-P_n)\psi,\quad
\Delta_n=(P_{n+1}-P_n)\psi.
$$

则 $\Delta_n$ 两两正交，且存在极限 $x_\infty$。令 $e_\infty=\psi-x_\infty$，则

$$
\boxed{x_\infty=x_0+\sum_{n=0}^\infty\Delta_n,\qquad
\|e_n\|^2=\|e_\infty\|^2+\sum_{j\ge n}\|\Delta_j\|^2.}
$$

此外，$e_n\to0$ 当且仅当
$\psi\in\overline{\bigcup_n\operatorname{ran}P_n}$。

**证明。**

递增正交投影满足 $P_nP_{n+1}=P_n$，故 $D_n=P_{n+1}-P_n$ 为正交投影。
不同 $D_n$ 的像空间互相正交，并与 $\operatorname{ran}P_0$ 正交。
望远镜式给

$$
x_n=x_0+\sum_{j<n}\Delta_j,\qquad
\|x_n\|^2=\|x_0\|^2+\sum_{j<n}\|\Delta_j\|^2\le\|\psi\|^2.
$$

因此平方和收敛，正交性使 $x_n$ 为 Cauchy 列。
其极限是 $\psi$ 在闭空间 $\mathcal M=\overline{\bigcup_n\operatorname{ran}P_n}$ 上的投影。
$e_\infty\perp\mathcal M$，所以
$e_n=e_\infty+\sum_{j\ge n}\Delta_j$ 是正交分解，得到尾式与零残差判据。

∎

这把静态本体的读出精化表达得很直接：$\psi$ 固定，内部读出的分解逐层改变。
若 $\|\psi\|=1$，令 $q_n=\|e_n\|^2$，在 $q_n>0$ 时取
$\alpha_n=\|\Delta_n\|^2/q_n$，则

$$
q_{n+1}=(1-\alpha_n)q_n,\qquad
\|x_{n+1}\|^2=\|x_n\|^2+\alpha_nq_n.
$$

归一总量保持；剩余质量的乘法递推与新增内容的正交级数是同一分解的两种表达。
递归总能收敛到可见闭子空间中的投影，收敛到整个目标则另需覆盖条件。

在固定 $\mathbb C^5$ 中，正交投影至多有五次严格秩增加。
无限非平凡正交精化需要增长的内部载体或记录空间；重复使用同一个五态更新则是另一种递归。
每个分解有明确内部酉记录实现，令 $\sigma_x$ 为二元记录的翻转算子：

$$
U_n=P_n\otimes I+(I-P_n)\otimes\sigma_x,\qquad U_n^*U_n=I,
$$

$$
U_n(\psi\otimes\lvert0\rangle)=P_n\psi\otimes\lvert0\rangle+(I-P_n)\psi\otimes\lvert1\rangle.
$$

这里记录因子属于同一整体。向量内积 $\langle x_n,e_n\rangle=0$ 不意味着整个纯态中的
跨扇区算子 $x_ne_n^*$ 消失；标量 Gram 不取代完整量子相关。

<a id="thm:neumann"></a>

### 定理 7.2（可取得的关系缺陷给出未知误差的修正级数）

设 Banach 空间上的有界线性算子 $A$ 满足 $\|A\|\le q<1$，
目标由 $x_*=b+Ax_*$ 定义。对任意当前结果 $x$，令关系缺陷

$$
r=b+Ax-x.
$$

则未知残差 $e=x_*-x$ 满足

$$
\boxed{e=Ae+r=\sum_{j=0}^{\infty}A^jr,\qquad
\|e\|\le\frac{\|r\|}{1-q}.}
$$

有限修正的尾误差为

$$
\left\|e-\sum_{j=0}^{m-1}A^jr\right\|
\le\frac{q^m}{1-q}\|r\|.
$$

**证明。**

首先 $x_*=\sum_{j\ge0}A^jb$ 在范数中收敛并满足目标关系；两个解之差 $h=Ah$ 强制 $h=0$。
目标关系减去当前结果得 $e=Ae+r$。
级数 $\sum A^jr$ 绝对收敛，其和满足同一个残差方程，唯一性给等式。
范数界和尾界直接来自几何级数。

∎

这条定理的有效内容是：可以不用先知道目标，只通过已知关系的残差 $r$ 控制未知误差。
但 $A,b,r$ 的取得与共同收缩证书必须真实供应；不能把未知误差改名为“关系读数”便认为已知。

<a id="cor:fibreseries"></a>

### 推论 7.3（固定三轴纤维上的五模式修正级数）

固定一个内部三轴点 $u=(X,Y,Z)$ 与目标交叉比 $\vartheta_*>0$，
令 $p_*$ 为混合坐标定理给出的唯一目标律。对 $0\le\kappa<1$，定义列随机更新

$$
T_\kappa=\kappa I+(1-\kappa)p_*\mathbf1^T.
$$

对任意同三轴初始律 $p$，每次更新保持这三个均值，且

$$
T_\kappa^np=p_*+\kappa^n(p-p_*),\qquad
\operatorname{TV}(T_\kappa^np,p_*)=\kappa^n\operatorname{TV}(p,p_*).
$$

关系缺陷 $r=T_\kappa p-p$ 满足

$$
p_*-p=\sum_{j\ge0}T_\kappa^jr=\sum_{j\ge0}\kappa^jr,
\qquad
\left\|p_*-p-\sum_{j<m}\kappa^jr\right\|_1
=\kappa^m\|p_*-p\|_1.
$$

**证明。**

$p_*\mathbf1^T$ 为幂等随机矩阵，且其与 $I$ 的上述凸组合仍随机。
两个律同三均值，故每个凸组合仍同三均值。
在零总质量向量上，$T_\kappa$ 恰为乘以 $\kappa$，所以迭代式、级数及尾式均直接成立。

∎

这里给出了一个真正保持归一化、留在同三轴纤维内、修正隐藏关系的有限模式递归。
它以声明的 $p_*$ 为目标；若选 $\vartheta_*=1$，就是向该纤维的最大熵截面收缩。
这个构造不保证未知真实来源恰有该目标关系，也不把依赖未知输入才选定的 $p_*$ 当成一个预先固定的通道。

沿用 v35 的内容投影 $\Pi$，若 $T\Pi=\Pi T=\Pi$，且 $T$ 在 $\ker\Pi$ 上收缩，
取 $Q=\operatorname{id}-\Pi$、$A=T|_{\ker\Pi}$，则

$$
\sum_{j\ge0}T^jQ=(I-A)^{-1}Q.
$$

完整空间的和一般却不收敛，因为

$$
\sum_{j=0}^{m-1}T^jX=m\Pi X+\sum_{j=0}^{m-1}A^jQX.
$$

当 $\Pi X\ne0$ 时，前项线性增长而后项有界。
所以需先固定应保存的内容，再对其余误差方向求收敛级数。

<a id="section-8"></a>

## 8　每层归一之后，还需要足够的累计改进

<a id="thm:variable"></a>

### 定理 8.1（非均匀收缩与实际误差比例）

令 $\Pi$ 为 CPTP 投影，$Q=\operatorname{id}-\Pi$，并取

$$
T_n=\Pi+\kappa_nQ=\kappa_n\operatorname{id}+(1-\kappa_n)\Pi,\qquad 0\le\kappa_n<1.
$$

则

$$
T_{n-1}\cdots T_0=\Pi+\left(\prod_{j<n}\kappa_j\right)Q.
$$

若所有 $\kappa_n>0$，则

$$
\boxed{\prod_{n\ge0}\kappa_n=0
\quad\Longleftrightarrow\quad
\sum_{n\ge0}(1-\kappa_n)=\infty.}
$$

若实际 CPTP 更新 $\Phi_n$ 满足 $\Pi\Phi_n=\Pi$，并且
$D(\Phi_n(\rho),T_n(\rho))\le\eta_n$ 对全部输入态 $\rho$ 成立，
定义 $\rho_{n+1}=\Phi_n(\rho_n)$，则在半迹距离中

$$
D_n\le\left(\prod_{j<n}\kappa_j\right)D_0
+\sum_{k<n}\eta_k\prod_{j=k+1}^{n-1}\kappa_j,
\quad D_n=D(\rho_n,\Pi\rho_0).
$$

条件

$$
\sum_n(1-\kappa_n)=\infty,\qquad
\frac{\eta_n}{1-\kappa_n}\longrightarrow0
$$

足以推出 $D_n\to0$。

**证明。**

$\Pi Q=Q\Pi=0$，幂等性使乘积只留下同类项，得到精确公式。
令 $a_n=1-\kappa_n$。由 $\log(1-a_n)\le-a_n$，发散的 $\sum a_n$ 强制乘积为零。
若 $\sum a_n<\infty$，尾部 $a_n\le1/2$，且 $-\log(1-a_n)\le2a_n$；
所有因子正，故乘积严格正。
实际保内容保证 $\Pi\rho_n=\Pi\rho_0$，一步三角不等式给
$D_{n+1}\le\kappa_nD_n+\eta_n$，归纳得到乘积卷积界。
对任意 $\epsilon>0$，尾部 $\eta_n\le\epsilon a_n$，所以
$D_{n+1}-\epsilon\le(1-a_n)(D_n-\epsilon)$。
所有尾乘积都趋零，故 $\limsup D_n\le\epsilon$，再令 $\epsilon\downarrow0$。

∎

若无误差且某一层 $\kappa_n=0$，残差从该层起消失，不需无限和判据。
有持续注入误差时，早期的一个零系数不能清除后来的误差，所以稳健定理使用全部尾部的累计改进条件。
例如 $\kappa_n=(n+1)/(n+2)$ 给精确乘积 $1/(n+1)$；统一收缩间隙并非必要。
但若 $\eta_n=c/(n+2)$，标量递推恰有
$D_n=(D_0+cn)/(n+1)\to c$：单步误差趋零，仍可留下非零残差。

<a id="thm:abel"></a>

### 定理 8.2（归一历史级数及有限尾质量）

设同一有限维载体上的 CPTP 映射 $T$ 与 CPTP 投影 $\Pi$ 满足 $T\Pi=\Pi T=\Pi$，
其中 $\Pi^2=\Pi$、$Q=\operatorname{id}-\Pi$，
$A=T|_{\ker\Pi}$ 在自伴迹范数上收缩率为 $q<1$。
对 $0\le\lambda<1$，定义

$$
\mathcal A_\lambda=(1-\lambda)\sum_{n\ge0}\lambda^nT^n.
$$

它是一个归一 CPTP 历史混合，且

$$
\mathcal A_\lambda
=\Pi+(1-\lambda)(I-\lambda A)^{-1}Q,
$$

$$
\boxed{D(\mathcal A_\lambda\rho,\Pi\rho)
\le\frac{1-\lambda}{1-\lambda q}D(\rho,\Pi\rho).}
$$

完整保迹的有限截断

$$
\mathcal A_{\lambda,m}
=(1-\lambda)\sum_{n=0}^{m-1}\lambda^nT^n+\lambda^mT^m
$$

对全部输入及内部参考满足
$d_{\rm ref}(\mathcal A_{\lambda,m},\mathcal A_\lambda)\le\lambda^m$。

**证明。**

非负权重之和为一，通道级数在有限维中收敛且保持 CPTP。
代入 $T^n=\Pi+A^nQ$，分别求几何级数，得到算子式与距离界。
无限尾部总质量为 $\lambda^m$，它乘以一个归一通道；有限截断把这份质量放到 $T^m$。
两归一通道的同输入半迹距离至多一，张量内部参考后亦然，故误差不超过该尾质量。

∎

这里归一化的是明确的历史权重，完整尾质量被保留。
它给一类可审查的“递归加级数加归一化”，并不证明该历史混合或其深度选择已经实际取得。

<a id="section-9"></a>

## 9　项目自身的历史级数：可归一化区间与精确尾误差

基础公式卷 §12.5 的对象是带既定跨窗守卫的实际接续历史：最高外接缝固定零，最低输出自由，
单位位零，允许空窗及长度零的空词。在这些确切边界条件下，长度 $L$ 的历史数为

$$
a_L=F_{3L+2},\qquad a_0=1,\quad a_1=5,\quad
a_{L+2}=4a_{L+1}+a_L.
$$

来源已给形式生成函数

$$
\mathcal Z(t)=\sum_{L\ge0}a_Lt^L=\frac{1+t}{1-4t-t^2}.
$$

边界守卫变更可能改变这个序列；可见几何格点计数的另一个生成函数
$(1+t)/(1-t)^4$ 也不与它等同。[2](#bib-foundation)

<a id="thm:historyseries"></a>

### 定理 9.1（实际历史权重的归一化与截断误差）

对每个合法长度 $L$ 历史赋权 $t^L$，其中 $t\ge0$。
全部有限历史可以用有限正总量归一化，当且仅当

$$
\boxed{0\le t<\sqrt5-2.}
$$

在该区间，令 $P_t(h)=t^{|h|}/\mathcal Z(t)$，
并将长度至多 $m$ 的历史重新归一为 $P_t^{\le m}$。
对每个整数 $m\ge0$，精确尾误差为

$$
\boxed{\operatorname{TV}(P_t,P_t^{\le m})=P_t(|h|>m)
=\frac{t^{m+1}(a_{m+1}+t a_m)}{1+t}.}
$$

**证明。**

将递推乘以相应幂次并逐项相加，得到形式恒等式
$(1-4t-t^2)\mathcal Z(t)=1+t$。
计数递推的特征根为 $2\pm\sqrt5$，且增长根的系数为
$(3+\sqrt5)/(2\sqrt5)>0$。
故 $a_L$ 按 $(2+\sqrt5)^L$ 增长，非负级数恰在
$t<(2+\sqrt5)^{-1}=\sqrt5-2$ 时收敛；在边界，单项亦不趋零。
在收敛域，令 $S_m(t)=\sum_{L=0}^{m}a_Lt^L$，递推给

$$
\mathcal Z(t)-S_m(t)
=\frac{a_{m+1}t^{m+1}+a_mt^{m+2}}{1-4t-t^2}.
$$

除以 $\mathcal Z(t)$ 得尾概率。原律与其在长度不超过 $m$ 上的条件律，
在保留集合内的总质量差等于被删尾质量，集合外的差也等于该量；半 $\ell^1$ 距离即为尾质量。

∎

这是真正以项目原生历史为索引的递归级数。有限层的归一化、形式级数恒等式和无限层的可归一化互不混同。
即使有理函数在某个收敛域外的点仍可代数求值，也不能将该值当成已发散的非负历史权重之和。
历史长度是同一静态整体中的内部记录索引，不需要引入整体外的时间参数。

<a id="section-10"></a>

## 10　误差能否实际读出：本轮新增的紧族有限观察接口

前述误差界需要读数供应。项目当前新增的
`exists_uniform_finite_readout_variation`
把既有固定有限误差族的结论扩展到*对偶范数紧*的误差族。
下面先忠实陈述其条件，再说明它与本稿稳定推理的连接。[4](#bib-finiteobs)

<a id="thm:finiteobs"></a>

### 定理 10.1（来源已有：范数紧误差族的统一有限读出）

设 $\mathcal X$ 为紧、零维、Hausdorff 的 Borel 空间，
$q_i:\mathcal X\to O_i$ 为连续的有限离散传感器，且全族 $\{q_i\}$ 分离点。
令 $\{s_a\}_{a\in A}$ 为有限有符号 Borel 测度族，正负 Jordan 部分均正则。
设积分泛函

$$
\Lambda_{s_a}:C(\mathcal X,\mathbb R)\to\mathbb R,
\qquad f\mapsto\int f\,ds_a
$$

的像集在算子范数中紧。则对每个 $\epsilon>0$，存在同一个有限索引集 $J$，使全部 $a$ 均有

$$
\boxed{\|s_a\|_{\rm var}-\epsilon
<\|(q_J)_*s_a\|_{\rm var}\le\|s_a\|_{\rm var},}
\qquad q_J=(q_i)_{i\in J}.
$$

> **编校注（测度族的量词）**：原稿上文“令 `{s_a}_{a∈A}` 为有限有符号 Borel 测度族，正负 Jordan 部分均正则”原句保留。“有限”在此指每个有符号测度有限；索引集 `A` 可任意，并非要求整个族只有有限项。所引固定提交中 `exists_uniform_finite_readout_variation` 的族指标为任意类型 `A : Type z`，另以积分泛函像集的算子范数紧性为前件。证明中的有限球心子族是从该紧性取得的。若原族为空，统一结论为空真，可取空的有限读出。

**证明（紧族扩展的纸面证明）。**

有限族的共同有限读出由来源既有定理供应。
记一个给定读出丢失的变差为
$L_J(s)=\|s\|_{\rm var}-\|(q_J)_*s\|_{\rm var}\ge0$。
正则测度的 Riesz 范数等式，以及连续函数拉回不增上确界范数，给

$$
L_J(s)\le L_J(t)+2\|\Lambda_s-\Lambda_t\|.
$$

具体地，源端范数变化至多为该对偶距离，输出端范数变化也至多为该距离，二者相加即可。
由范数紧性，选择以原族成员 $\Lambda_{s_b}$ 为球心的有限个半径 $\epsilon/4$ 开球覆盖全族；
给这些球心应用有限族结论，获得共同 $J$，使各球心的损失小于 $\epsilon/2$。
任意族成员与某个球心的对偶距离小于 $\epsilon/4$，代入转移界得
$L_J(s)<\epsilon/2+2(\epsilon/4)=\epsilon$。
右侧不等式是推前不增加总变差。

∎

因此，在这些前件真实满足时，同一个有限联合读出映射能够在变差范数意义下，
同时近似保留整个允许误差族；这不等于单次样本就能估计未知总变差。
若取 $s_a=p_a-\tilde p_a$ 为概率差，则其总变差范数是相应半距离的两倍。
取 $\epsilon_n\downarrow0$ 并将各次有限集合累积取并，能够得到递增的有限读出，
其对整个紧族的损失一致趋零；保留更多传感器不会增大损失。
但该存在性并未供应具体所需预算、取得算法、深度代价或固定三轴表示。

<a id="prop:finiteobstruction"></a>

### 命题 10.2（不能用固定有限读出统一捕获任意误差）

沿用本节对 $\mathcal X$ 的假设，若 $\mathcal X$ 无限，考虑全部 Dirac 差 $\delta_x-\delta_y$。
任意固定有限联合有限值读出 $q_J$ 都存在某个非零误差，其读出为零，而源总变差范数为二。

**证明。**

$q_J$ 的值域有限，故存在不同 $x,y$ 位于同一纤维。
于是 $(q_J)_*(\delta_x-\delta_y)=0$，但两个不同点质量的差总变差为二。
另外取两两不同的 $x_0,x_1,\ldots$，则
$\Lambda_{\delta_{x_n}-\delta_{x_0}}$ 两两范数距离为二，故该误差类不是范数紧集。
它没有满足上一来源定理的关键前件。

∎

此处“紧”指算子范数拓扑，不能用一般弱紧性替换。
原五模式的完整五函数基确能捕获该有限经典模型中的全部状态误差；
对更大的内部载体，仍需证明允许误差族是否保留这种有限可观测结构。

<a id="section-11"></a>

## 11　本轮可以确定的语义与后续证明合同

<a id="summary-table"></a>

| 所讨论的对象 | 准确的完整信息 | 任意四推一的前件 |
| --- | --- | --- |
| 五事件质量 | $w_0,w_2,w_3,w_5,w_{25}$ | 总量 $N$ 独立已知，缺失位置已知。 |
| 五语义矩 | $N,X,Y,Z,K$ 是同尺度的完整线性坐标 | 原本不成立；固定正交叉比后，在严格正相容域成立。 |
| 归一混合坐标 | $(X,Y,Z,\chi)$ 为四个独立坐标 | $N=1$ 已是约定；删除独立关系读数仍会丢失信息。 |
| 结果与误差关系 | Gram 的尺度与归一三轴；或有符号差的质量与正负记录 | 必须指定误差类型，保留尺度，并控制相消或支持边界。 |

对用户的主张，本文给出的最强准确表述是：

> 原五模式恰有常数一、三个占据轴和一个联合关系组成的完整函数基。
> 在额外给定可解关系、保持共同尺度且远离病态边界时，它可以成为稳定的四推一恢复结构。
> 若这一状态摘要对下一层更新闭合，关系缺陷又满足正交消耗或足够强的累计收缩，
> 结果与误差的递归便有严格的级数表示、归一化方案及有限尾误差证书。

闭合解决“下一层究竟由什么决定”；可观测性解决“这些量是否能取得”；
逆映射条件数解决“读数扰动会被放大多少”；尾部控制解决“无限递归是否收敛”。
这四个条件承担不同任务，不能由一个归一化式同时替代。
同一个酉变换满足 $\|U\psi-U\phi\|=\|\psi-\phi\|$，所以酉性本身仅保持该误差距离；
若所读结果误差要下降，必须明确内容、内部记录和被读出的部分，或给出前述有约束的修正递归。
全局的内部酉记录与局部的误差收缩可以相容。

本轮新增的纸面推导主要是：固定交叉比的全坐标四推一及其条件数、
两点关系差的锐双曲正切界、结果–误差相消控制、派生误差关系与分母级数、固定纤维的显式收缩级数、
非均匀改进与注入误差比例条件，以及原生历史的精确截断尾式。
五函数基、混合坐标双射、最大熵截面、四角闭合和紧族有限读出均按来源已有结果使用。
没有把这些新推论报告为仓库已实现、已执行验证或已实际取得的协议。

<a id="bibliography"></a>

## 固定来源与证据范围

<a id="bib-head"></a>

### [1]

[固定提交：38076d7a280e0e8186c3d5507e3dea59b6d4803c](https://github.com/the-omega-institute/trureturing/commit/38076d7a280e0e8186c3d5507e3dea59b6d4803c)。
2026-10-30 19:23:01 UTC，合并 #24362。
只读核对公共源码与 Git blob；无仓库修改或形式验证执行。

<a id="bib-foundation"></a>

### [2]

[AURIC FIB atom pyramid：Foundational formulas and relations](https://github.com/the-omega-institute/trureturing/blob/38076d7a280e0e8186c3d5507e3dea59b6d4803c/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
本稿使用 §2.2 的五函数与事件基，§§4–5 的隐藏纤维，§9 的乘积补全与最大熵，
§12.5 的守卫历史计数，以及 §§14.4–14.6 的均值、联合分支和反馈闭合。

<a id="bib-mixed"></a>

### [3]

[FiveModeMixedCoordinates.lean](https://github.com/the-omega-institute/trureturing/blob/38076d7a280e0e8186c3d5507e3dea59b6d4803c/D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.lean)。
完整读取定义及 `mixed_coordinates_global_chart`：
严格正归一五模式律与内部三轴点、实隐藏对数交叉比的唯一对应。

<a id="bib-finiteobs"></a>

### [4]

[FiniteObservationVariation.lean](https://github.com/the-omega-institute/trureturing/blob/38076d7a280e0e8186c3d5507e3dea59b6d4803c/D5/S3/Topology/Measures/FiniteObservationVariation.lean)。
本轮相对 v35 新增 `exists_uniform_finite_readout_variation`；
使用完整定理前件、有限网证明及变差损失转移界。范数紧性不可替换为一般弱紧性。

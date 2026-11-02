# 正历史回返、手性原子与椭圆读出

从有限正反参照对重建实际量子门

AURIC v84：一个完整候选及其量子理论

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮承接 v83，研究四个相连的直觉：正交切向定义原子面积，内生手性只允许正向门，逆作用由继续追加门来实现，回溯与方向限制使圆变为椭圆。
可严格保留的核心是：执行回返与正历史增长能够共存；单向原生调用可以通过继续绕行产生逆的端点作用。
正交本身没有提供非零最小面积，手性本身也没有指定椭圆。

本文只提出一个新候选 $C_{84}$。沿用共同复正核、有限完整单位载体、二元不扩张与有限复方向校准，仅要求一个实正交框的有限组正反参照对能够通过同一门的正幂共同回近原位。证明先把正历史回返转成锚点反号，再以正反比较夹定全部坐标，得到原实际映射的复线性酉性。反向证明任一有限维酉门都有任意晚的统一正幂回返，并给出纯解析存在上界。因此正向近似逆成为结论；精确正幂逆则需要有限阶，而具有更多原生门的正词菜单另有其精确逆关系。

项目已有的水平几何、接触曲率与回路相位作为继承接口使用；V80 的有限锚刚性作为本轮证明的后续环节。FIB 原生门 $K_j^{10}=I$ 给出九次正向调用实现逆的实际例子，并与另一固定五模式菜单的精确逆障碍对照。随后给出正交面积的缩放反例、单向四步圆反例、严格同手性非椭圆反例，证明正二次响应及线性分支读出怎样产生椭圆。能量由实际切向生成元与时钟刻度界定，逆门成本另由原生控制供应界定。最后明确接回有限维量子态、酉演化、Born 读出、密度矩阵、张量积与仪器的全部依赖。

数学均为解析推导，未执行数学程序、数值试验或搜索枚举。

## 目录

- [1. 版本承接、项目依据与本轮新增接口](#section-1)
- [2. 定义：正历史、执行与真正的回溯](#section-2)
- [3. 正交切向、关系面积与有限三维提升](#section-3)
- [4. 一个正交、单向、可回溯却仍是圆的完整例子](#section-4)
- [5. 唯一新候选：有限正反参照对的正历史回返](#section-5)
- [6. 反向定理：酉门具有任意晚的统一正向回返](#section-6)
- [7. 反向删除审计：每项约束承担什么](#section-7)
- [8. 原生实例：项目中的十步回返与另一菜单的逆障碍](#section-8)
- [9. 更大结构：增长历史之上出现可逆执行闭包](#section-9)
- [10. 有向回路留下什么：继承的接触相位而非最小面积](#section-10)
- [11. 椭圆的充分条件与反例](#section-11)
- [12. 几种椭圆必须保留各自的来源](#section-12)
- [13. 最接近“不可压缩面积”的量子结论](#section-13)
- [14. 能量、逆门成本与内生时钟](#section-14)
- [15. 由本轮候选完整接回有限维量子规则](#section-15)
- [16. 一段白话与本轮结论边界](#section-16)

<a id="section-1"></a>

## 1. 版本承接、项目依据与本轮新增接口

本轮记为 v84，直接承接对话 v83。可核验的项目基线仍是

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`。

实时读取未取得更新 HEAD，因此本文不声称覆盖未核读提交。本轮重新核读了五份固定来源的相关正文：整体静态相容纤维理论、FIB 相干重建续卷 V、V74、V80，以及前轮 v83 的明确结果。文末链接均固定到上述提交。

| 来源 | 已有结论 | v84 的使用位置 |
| --- | --- | --- |
| 整体主文 | 正历史追加不同于执行逆；固定菜单可有精确逆障碍 | 历史、成本及菜单对照 |
| FIB 续卷 V | 完整正向单位脉冲，$K_j^{10}=I$ | 九次同向调用的逆实现 |
| V74 | $g,\omega,J$、二元面积余量、接触曲率、回路相位、能量方差速度 | 正交、手性和能量的继承接口 |
| V80 | 四周锚校准与不扩张推出实际等距；分支椭圆预算 | 把本轮回返转成锚刚性 |
| v83 | 对径输出闭合与不扩张推出酉性 | 本轮改由正历史供应反锚关系 |

V80 直接要求有限锚上的 $F(i^k a_j)=i^kF(a_j)$，$k=1,2,3$。v84 的新增连接是：**用实际正迭代的回返，推得有限框上的反号条件**，再应用既有锚刚性。它不是对整仓库或数学文献的首次发现声明。

所有参照、程序、时钟与记录均在 $Omega$ 内。声明一个有限载体 $H$ 不等于声称整个 $Omega$ 有限。下文的回返只作用于明确的执行载体；若把永远增长且可读的历史也纳入内容比较，该完整内容未必回返。

**白话图景。**本轮不重新打开已经讨论过的距离、面积与相位问题。新的问题是：即使历史只能向前追加，能不能从内部回返关系推出完整门的可逆结构？答案可以肯定，但要把有限执行内容和持续增长的记录放在各自的类型里。

<a id="section-2"></a>

## 2. 定义：正历史、执行与真正的回溯

<a id="definition-2-1"></a>

#### 定义 2.1（正历史与执行）

在允许任意串接的一个固定原生门菜单中，给定字母表 $\Sigma_+$，历史是有限正词 $w\in\Sigma_+^*$，长度记为 $\ell(w)$。追加一个原子调用 $a$ 时

$$
\ell(wa)=\ell(w)+1,\qquad
\operatorname{Exec}(wa)=U_a\operatorname{Exec}(w).
$$

字按实际调用次序书写，算子按右端先作用。

一般受护卫限制的菜单须另外保留合法域；本定义不自动增加其串接权限。后文关于执行幺半群的结论只用于已声明串接闭合的菜单。

若合法正词 $v$ 满足 $\operatorname{Exec}(v)=U_a^{-1}$，则

$$
\operatorname{Exec}(wav)=\operatorname{Exec}(w),\qquad
\ell(wav)=\ell(w)+1+\ell(v)>\ell(w).
$$

这是工作内容回溯而历史仍增长的精确形式。当长度或日志属于可读接口时，$w$ 与 $wav$ 是不同完整内容；它们只在执行读出商中相同。

#### 命题 2.2（追加逆作用不等于删除事件）

在历史表示 $\ell^2(\Sigma_+^*)$ 上定义 $S_a\ket w=\ket{wa}$。若存在另一个原生字母 $\bar a$ 满足 $U_{\bar a}=U_a^{-1}$，仍有

$$
S_{\bar a}S_a\ket w=\ket{wa\bar a}\ne\ket w,
\qquad S_{\bar a}\ne S_a^\dagger.
$$

**证明。**$S_a^\dagger$ 删除词尾 $a$，在不以 $a$ 结尾的基向量上为零；$S_{\bar a}$ 则向所有词尾追加一个新字母。二者作用不同。

长度算子 $N_{\rm hist}\ket w=\ell(w)\ket w$ 在有限支撑共同定义域上满足

$$
[N_{\rm hist},S_a]=S_a.
$$

该公式和历史表示已在整体主文第 7 节给出 [1](#ref-omega)。把历史基写成正交向量是一种声明的记录表示；不能仅凭存在路径索引，就认定物理上已经生成可区分的路径记录。

#### 定义 2.3（三种逆）

数学逆是满足 $VU=UV=I$ 的算子。原生逆实现是一个合法正词，其执行等于该逆。逆路径则要求从终态开始，逐点反向重走指定历史。三者的类型与可用条件不同。

**白话图景。**搜索回溯会把工作区恢复到先前状态，但“做过一次尝试，又撤回”仍能写进日志。量子门字也可以如此。增加一个逆作用，是增加一个新事件；它没有把过去的一页撕掉。

<a id="section-3"></a>

## 3. 正交切向、关系面积与有限三维提升

沿用 V74 的共同复结构，内积取第二变量线性。在归一态 $\psi$ 的水平切空间 $\psi^\perp$ 上记

$$
g_0(u,v)=\operatorname{Re}\langle u,v\rangle,\qquad
\omega_0(u,v)=\operatorname{Im}\langle u,v\rangle,\qquad Ju=iu.
$$

项目采用的有量纲标度是

$$
g=2\hbar g_0,\qquad \omega=2\hbar\omega_0,
\qquad \omega(u,v)=g(Ju,v).
$$

这里的 $\hbar$ 是既有相位、时间与物理单位标定的一部分。

#### 定义 3.1（三种正交）

态正交是 $\langle\psi,\phi\rangle=0$。实切向正交是 $g_0(u,v)=0$。复切向正交是 $\langle u,v\rangle=0$，它还使 $\omega_0(u,v)=0$。不同点的切向要先声明共同嵌入或平行运输，才谈它们的夹角。

#### 定理 3.2（同一个二元 Gram 关系的三维分解）

设 $u,v\ne0$，令

$$
D=\lVert u\rVert^2\lVert v\rVert^2-\lvert\langle u,v\rangle\rvert^2\ge0.
$$

则

$$
A_0^2:=\lVert u\rVert^2\lVert v\rVert^2-g_0(u,v)^2
=\omega_0(u,v)^2+D,
$$

并且

$$
\boxed{
r_1=\frac{g_0(u,v)}{\lVert u\rVert\lVert v\rVert},\quad
r_2=\frac{\omega_0(u,v)}{\lVert u\rVert\lVert v\rVert},\quad
r_3=\frac{\sqrt D}{\lVert u\rVert\lVert v\rVert},\quad
r_1^2+r_2^2+r_3^2=1,\quad r_3\ge0.
}
$$

有量纲面积满足

$$
A_g^2-\omega(u,v)^2=(2\hbar)^2D,\qquad A_g=2\hbar A_0.
$$

**证明。**把 $|\langle u,v\rangle|^2$ 分成实部平方与虚部平方，代入定义即可。$D\ge0$ 来自二阶 Gram 正性。零向量边界不作上述归一化。

这正是 V74 第 5、9 节的二元几何接口 [2](#ref-v74)。这些三维点是同一正核的局部关系坐标，不是整个态空间的三维嵌入。

#### 命题 3.3（何时正交与手性选出唯一的四分之一周方向）

对非零 $u,v$，下列条件合起来等价于 $v=Ju$：

$$
g_0(u,v)=0,\qquad \lVert u\rVert=\lVert v\rVert,
\qquad D=0,\qquad \omega_0(u,v)>0.
$$

**证明。**$D=0$ 使 $v=cu$。实正交给 $\operatorname{Re}c=0$，等长给 $|c|=1$，正手性给 $\operatorname{Im}c>0$，故 $c=i$。反向直接代入。

若删去 $D=0$，在水平复维数至少二时可取 $u=e_1$、$v=(ie_1+e_2)/\sqrt2$；它们等长、实正交且有正辛面积，却不满足 $v=Ju$。因此“没有额外正余量”也承担了一项约束。

#### 命题 3.4（正交没有给出最小正面积）

取 $\psi=e_0$，

$$
u_\varepsilon=\varepsilon e_1,\qquad
v_\varepsilon=i\varepsilon e_1,\qquad \varepsilon>0.
$$

它们水平、实正交、等长、有正手性且 $D=0$，但

$$
A_0=\omega_0(u_\varepsilon,v_\varepsilon)=\varepsilon^2,
\qquad A_g=2\hbar\varepsilon^2\longrightarrow0.
$$

**证明。**逐项代入即可。这些切向也能由反自伴生成元

$$
K_1=\varepsilon(\ket1\bra0-\ket0\bra1),\qquad
K_2=i\varepsilon(\ket1\bra0+\ket0\bra1)
$$

作用于 $e_0$ 产生，因此反例没有离开酉动力学。

即使把方向归一，实际小步为 $\delta s\,u,\delta t\,v$，面积仍乘上 $\delta s\,\delta t$。微积分的面积元不是“最小非零小方块”。

#### 命题 3.5（任意相邻瞬间直角转向与非零光滑速度不相容）

若 $\gamma$ 是 $C^1$ 曲线，且对某个 $t$ 和一列 $h_n\to0$ 有 $\operatorname{Re}\langle\dot\gamma(t),\dot\gamma(t+h_n)\rangle=0$，则 $\dot\gamma(t)=0$。流形上经连续平行运输比较时结论相同。

**证明。**由速度连续性取极限，得到 $\lVert\dot\gamma(t)\rVert^2=0$。

**白话图景。**正交选出两条比较方向，手性选出其中的旋转次序。再要求等长与没有额外正余量，确实能锁定一个四分之一周关系。但它没有规定必须走多远。方向可以保持不变，步长却任意缩小。因此原子调用的不可细分性，要来自明确的原生菜单，而不能单由微积分面积推出。

<a id="section-4"></a>

## 4. 一个正交、单向、可回溯却仍是圆的完整例子

#### 定理 4.1（单向四步圆）

在共同 Hilbert 嵌入中取

$$
\gamma(s)=\cos s\,\ket0+\sin s\,\ket1,\qquad
U(s)=e^{-is\sigma_y}.
$$

规定唯一原生调用是 $G=U(\pi/2)$，只允许正追加。则两端切向正交，逆作用可由三个正调用实现，但轨迹始终是原圆：

$$
\dot\gamma(0)=\ket1,\qquad \dot\gamma(\pi/2)=-\ket0,
\qquad G^4=I,\qquad G^{-1}=G^3.
$$

**证明。**直接对 $\gamma$ 求导。由 $\sigma_y^2=I$，$U(s)=\cos s\,I-i\sin s\,\sigma_y$，所以四个正脉冲完成一圈，后三个正脉冲的端点作用等于第一脉冲的逆。

然而 $G=U(\pi/4)^2$。若半脉冲没有被原生菜单禁止，它在数学上仍可分解。在射线层 $G^2=-I$ 已返回；保留内部相位参照时需区分这个负号。两端切向的上述正交是共同嵌入中的比较；沿大圆作内禀平行运输时，正向单位切向本身相互平行。

```tex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Stealth,font=\small,scale=.9]
\begin{scope}[xshift=-3.5cm]
\draw[->,gray!65](-1.8,0)--(1.8,0);
\draw[->,gray!65](0,-1.8)--(0,1.8);
\draw[ink,very thick](0,0)circle(1.35);
\foreach \a in {22,112,202,292}
 {\draw[->,accent,thick](\a:1.35)arc[start angle=\a,end angle=\a+31,radius=1.35];}
\node[right]at(1.4,0){\(\ket0\)};
\node[above]at(0,1.4){\(\ket1\)};
\node[left]at(-1.4,0){\(-\ket0\)};
\node[below]at(0,-1.4){\(-\ket1\)};
\node[align=center,text width=5.8cm]at(0,-2.35)
{只许四分之一圈正向调用\\\(G^{-1}=G^3\)，形状仍是圆};
\end{scope}
\begin{scope}[xshift=3.5cm]
\draw[->,gray!65](-1.9,0)--(1.9,0);
\draw[->,gray!65](0,-1.8)--(0,1.8);
\draw[warm,very thick](0,0)ellipse[x radius=1.6,y radius=.9];
\draw[->,warm,thick](1.6,0)arc[start angle=0,end angle=55,x radius=1.6,y radius=.9];
\node[above]at(0,1.35){\(z^{\mathsf T}Qz=2E\)};
\node[align=center,text width=5.8cm]at(0,-2.35)
{正二次响应的两个方向不等\\椭圆来自 \(Q\) 的各向异性};
\end{scope}
\end{tikzpicture}
\caption{两个不同机制：正向回返决定可达端点；正二次型决定轨迹形状。图中椭圆为示意的精确二次曲线，不代表球面上的一般轨迹。}
\end{figure}
```

若“禁止切线”意为禁止负向速度，这个圆已经满足单向菜单而没有变成椭圆。若字面要求实际速度不沿实际轨迹的切线，则与切向量的定义冲突。若要求不断向同一侧弯曲，第 11 节仍有非椭圆反例。

**白话图景。**单行环路可以走回入口。逆作用也可以通过继续向前绕行得到，因此“回到哪里”与“沿哪条路回来”并不是同一条件。正交端点、单向原子调用和回溯，合起来仍没有把圆强制改成椭圆。

<a id="section-5"></a>

## 5. 唯一新候选：有限正反参照对的正历史回返

#### 定义 5.1（$C_{84}$ 的完整条件）

设 $H$ 为 $d\ge1$ 维复 Hilbert 空间，$F:S(H)\to S(H)$ 是同一有限执行载体上的实际完整续接。它可以合法地重复正调用。不预设线性、单射、满射、可微或原生逆。

取复正交单位框 $a_1,\ldots,a_d$，令

$$
B=\{a_1,ia_1,\ldots,a_d,ia_d\}.
$$

该实框张成整个声明载体，所有相位以同一内部参照比较。候选包括：

$$
\begin{aligned}
\lVert F(x)-F(y)\rVert&\le\lVert x-y\rVert &&(x,y\in S(H)), &&\tag{N}\\
F(ia_j)&=iF(a_j) &&(1\le j\le d), &&\tag{J}\\
\forall b\in B,\ \forall\varepsilon>0,\quad
\exists n\ge1:\quad
\max\{\lVert F^n b-b\rVert,\lVert F^n(-b)+b\rVert\}&<\varepsilon. &&\tag{$R_B^+$}
\end{aligned}
$$

同一正反对使用同一个 $n$；不同轴对不必预先共用步数。新接口是 $R_B^+$，N 与有限 J 沿用前轮关系条件。

这里共有 $2d$ 组正反对、$4d$ 个参照点。有限的是回返框，不是所有输入测试：N 仍覆盖整个声明单位球面。如果相位参照已经被商掉，$b$ 与 $-b$ 是同一射线，便不能直接使用这份幅度层证书。

**白话图景。**不用先规定一个门必须有外部逆。只要求有限组有符号参照在同一个正向门下可以共同回近原位，再把不扩张条件用于这些参照和任意输入，整张坐标网就会被锁住。

<a id="section-6"></a>

#### 定理 5.2（正历史回返迫出实际酉门）

满足 $C_{84}$ 时，存在唯一复线性酉算子 $U:H\to H$，使

$$
\boxed{F(x)=Ux\quad(x\in S(H)),\qquad U^\dagger U=UU^\dagger=I.}
$$

**证明。**分四步。

**第一步：回返锁定有限反锚。**对 $b\in B$，N 的迭代性给

$$
\lVert F^n b-F^n(-b)\rVert
\le\lVert Fb-F(-b)\rVert\le2.
$$

由 $R_B^+$ 与三角不等式，

$$
2<2\varepsilon+\lVert Fb-F(-b)\rVert.
$$

令 $\varepsilon\downarrow0$，得 $\lVert Fb-F(-b)\rVert=2$。两单位向量相距二，当且仅当互为反面，因此

$$
\boxed{F(-b)=-F(b),\qquad b\in B.}
$$

**第二步：正反比较锁定全部坐标。**对任意单位 $x$，N 分别用于 $(x,b)$ 和 $(x,-b)$，展开得

$$
g_0(Fx,Fb)\ge g_0(x,b),\qquad
g_0(Fx,Fb)\le g_0(x,b).
$$

故

$$
\boxed{g_0(Fx,Fb)=g_0(x,b)\quad(x\in S(H),\,b\in B).}
$$

**第三步：原实际映射实线性。**把 $B$ 排为 $b_1,\ldots,b_{2d}$，令 $c_j=F(b_j)$。取 $x=b_k$，得到 $g_0(c_k,c_j)=\delta_{kj}$。目标与输入同为 $2d$ 维实空间，故 $\{c_j\}$ 是完整实正交框。所以

$$
F(x)=\sum_{j=1}^{2d}g_0(Fx,c_j)c_j
=\sum_{j=1}^{2d}g_0(x,b_j)c_j.
$$

右端定义实线性正交算子 $U$，并在整个单位球面上等于原 $F$。

**第四步：有限 J 迫出复线性。**由 $U(ia_j)=iU(a_j)$ 及实线性，得到 $U(ix)=iU(x)$ 对所有 $x$ 成立。因此 $U$ 复线性，实内积保持随之给完整复内积保持。有限同维保证满射，故 $U^{-1}=U^\dagger$。完整框也保证唯一性。证毕。

本证明在反锚锁定之后应用 V80 的同类夹定结构 [3](#ref-v80)；与 v83 的区别是反面关系由实际正迭代回返供给。它没有假定整个门已经水平，也没有把一条指定态的切向冒充全输入生成元。

#### 命题 5.3（有限精度的直接后果）

若某一对在一个正步数 $n$ 的回返误差均小于 $0<\varepsilon\le1$，且 N 精确成立，则

$$
\lVert Fb+F(-b)\rVert^2
\le8\varepsilon-4\varepsilon^2\le8\varepsilon.
$$

**证明。**首步两输出距离至少 $2-2\varepsilon$，再用单位向量的平行四边形恒等式。

有限误差只给有限反锚误差；不能把一次近似回返报告成精确酉性的实验证书。

**白话图景。**两根参照原本在球的正反两端。如果每走一步都不能把距离拉大，却又能继续向前走、把这两根参照共同带回原位，那么第一步就不能把它们挤近。对完整坐标框的正反方向都如此，任何内容相对于这些参照的坐标就被锁死了。整个实际门因此只能保持完整关系，成为酉门。

<a id="section-7"></a>

## 6. 反向定理：酉门具有任意晚的统一正向回返

#### 定理 6.1（纯解析正幂回返及存在上界）

给有限维酉门 $U$、$\varepsilon>0$ 与任意整数 $L\ge1$，存在整数 $n\ge L$ 使

$$
\lVert U^n-I\rVert_{\rm op}<\varepsilon.
$$

更具体地，取整数 $Q>2\pi/\varepsilon$，可取

$$
L\le n\le LQ^d.
$$

**证明。**取谱表示 $U=\sum_{j=1}^d e^{i\theta_j}P_j$，允许重复列出本征相位。把 $d$ 维相位环面分成 $Q^d$ 个边长 $2\pi/Q$ 的半开方盒。考虑 $Q^d+1$ 个相位点

$$
kL(\theta_1,\ldots,\theta_d)\pmod{2\pi},
\qquad k=0,\ldots,Q^d.
$$

抽屉原理给 $k>\ell$ 落入同盒。令 $n=(k-\ell)L$，则各个相位的差模 $2\pi$ 都有绝对值小于 $2\pi/Q$ 的代表。使用 $|e^{is}-1|\le|s|$，得到

$$
\lVert U^n-I\rVert_{\rm op}
=\max_j|e^{in\theta_j}-1|
<2\pi/Q<\varepsilon.
$$

全部步骤是有限覆盖存在证明，没有运行枚举。这属于有限维统一量子回返的既有数学结构 [4](#ref-wallace) [5](#ref-bocchieri)；上界不主张最佳，也不保证实际搜索回返字便宜。

#### 推论 6.2（正向近似逆与候选的反向成立）

取 $L\ge2$，则

$$
\boxed{\lVert U^{n-1}-U^\dagger\rVert_{\rm op}
=\lVert U^n-I\rVert_{\rm op}<\varepsilon.}
$$

任一有限维酉门都满足 N、J、$R_B^+$，所以在本声明类型内，$C_{84}$ 与实际复线性酉门等价。

**证明。**第一式右乘 $U^\dagger$ 并用酉不变性。统一回返当然蕴含每个锚对的共同回返。证毕。

#### 命题 6.3（单门正幂菜单的精确逆）

只允许重复同一门 $U$ 时，存在正整数 $m$ 使 $U^m=U^\dagger$，当且仅当存在 $q\ge1$ 使 $U^q=I$。

**证明。**正向由 $U^{m+1}=I$。反向若 $q\ge2$，取 $m=q-1$；若 $U=I$，取 $m=1$。证毕。

只比较射线或通道时，精确条件改为 $U^q=e^{i\phi}I$ 的有限射影阶。保留内部相位参照时不能省掉该相位。有其他原生门时，精确逆可能由别的正词实现，上述必要性不适用于整个多门菜单。

**白话图景。**一个有限酉门的所有相位都在有限个圆上转。反复向前调用，总能让这些相位同时回到任意接近原位的位置。少走最后一步，就近似实现了逆门。精确绕回与任意接近是两个不同要求；相位周期恰好相容时，有限正词才能按此方式精确回返。

<a id="section-8"></a>

## 7. 反向删除审计：每项约束承担什么

#### 命题 7.1（删除回返会留下折叠）

在实正交框 $B=\{b_k\}_{k=1}^{2d}$ 中，遗漏某个轴对 $b_r,-b_r$。定义

$$
F\left(\sum_kx_kb_k\right)
=\sum_{k\ne r}x_kb_k+|x_r|b_r.
$$

则 F 保持球面并满足 N，固定所有正锚以及其他正反轴，因此有限 J 也成立；但它把 $-b_r$ 永久折到 $b_r$。

**证明。**实坐标绝对值不增加差值平方，故 N 成立；其余逐项检查。

这证明每个轴对在当前固定框形式里都有作用，不证明该方案在所有可能公理中绝对最弱。特别地，仅检查 $\pm a_j$ 不足：$F(z)_j=\operatorname{Re}z_j+i|\operatorname{Im}z_j|$ 保留这些点及正四分之一周校准，却折叠 $-ia_j$。

#### 命题 7.2（删除 N 后，精确周期仍可非酉）

取 $a>1$，

$$
B_a=\begin{pmatrix}0&a\\a^{-1}&0\end{pmatrix},
\qquad F_a(x)=\frac{B_ax}{\lVert B_ax\rVert}.
$$

则 $F_a^2=\mathrm{id}$，且 $F_a(ix)=iF_a(x)$，所以所有锚点在同一步数二精确回返。但 $F_a$ 不保持距离。

**证明。**$B_a^2=I$ 给归一化复合仍为恒等。取 $x=(e_1+e_2)/\sqrt2$、$y=(e_1-e_2)/\sqrt2$，则

$$
\lVert x-y\rVert^2=2,\qquad
\lVert F_a(x)-F_a(y)\rVert^2
=\frac{4a^2}{a^2+a^{-2}}>2.
$$

这明确排除了“只要能回溯就已经酉”的推断。

删除 J 时，复共轭保持所有距离且平方为恒等，却非复线性。删除完整有限框覆盖时，可取 $H=\mathbb C^d\oplus\ell^2(\mathbb N)$、$F=I_{\mathbb C^d}\oplus S$，其中 $S$ 为单边移位。有限锚全部放在 $\mathbb C^d$，被测锚点固定，N 和复线性都成立，然而 F 不满射。所以有限锚必须覆盖整个声明载体。

同一个 $n$ 的成对回返使证明直接作用于二元关系。本文不主张它在有限紧性背景下不能再削弱，也不把“新候选”解释为已经证明全局逻辑最弱的一组公理。

**白话图景。**没有回返，某条轴可以被折起来；没有不扩张，周期操作也可以来回拉歪关系；没有复方向，镜像式共轭仍会留下；没有完整覆盖，差别可以被送进未检验的无限尾部。反推的价值在于把每一个失败准确定位到哪一对内容、哪一段接口。

### 7.1 有限正反锚的直接见证

候选使用 $2d$ 个正反轴对，即 $4d$ 个幅度参照；输入槽 $x$ 仍为整个声明单位球面。若只抽查有限个未知输入，N 的全域夹定不能成立。若把反向参照换成射线等价类，也会丢失内部相位参照所提供的反号信息。

### 7.2 有限精度与实际实验

在误差预算为 $\varepsilon$ 时，命题 6.2 只给锚点反号的 $O(\sqrt\varepsilon)$ 级坐标误差；要报告近似酉门，还需给出全输入关系的误差范数和同一正幂步数。候选的精确等价只适用于数学上精确的 N、J 和 $R_B^+$。

**白话图景。**折叠、拉伸、共轭和未覆盖的尾部都是可以构造出来的失败模型。回返条件在这里承担的是反锚认证；不扩张和共同复方向仍各自承担自己的刚性作用。

<a id="section-9"></a>

## 8. 原生实例：项目中的十步回返与另一菜单的逆障碍

### 8.1 FIB 原生门给出精确正向逆

项目 FIB 相干重建续卷 V 第 1 节明确给出 [6](#ref-fibv)

$$
\zeta=e^{3\pi i/5},\qquad
K_j=\zeta[I+(\zeta-1)\mathcal P_j],\qquad
\mathcal P_j^2=\mathcal P_j=\mathcal P_j^\dagger.
$$

每次实际控制是完整正向单位脉冲，不允许半步、负时间或更改脉冲生成元。因为

$$
K_j=\zeta(I-\mathcal P_j)+\zeta^2\mathcal P_j,
$$

所以

$$
\boxed{K_j^{10}=I,\qquad K_j^{-1}=K_j^9.}
$$

这是一个明确合法的九次实现上界；本文没有另证所有中心的最短逆字。

#### 定理 8.1（有限阶原子使整个正词执行像已经是群）

若为每个原生 $U_a$ 指定正整数 $r_a$，满足 $U_a^{r_a}=I$，$r_a$ 无须为最小阶，则任一未读酉门正词 $w=a_1\cdots a_L$ 的执行逆，都可由正词实现：

$$
v=a_L^{\,r_{a_L}-1}\cdots a_1^{\,r_{a_1}-1}.
$$

零指数块取空字。其调用数至多 $\sum_k(r_{a_k}-1)$。

**证明。**$\operatorname{Exec}(w)=U_{a_L}\cdots U_{a_1}$，而 $\operatorname{Exec}(v)=U_{a_1}^{-1}\cdots U_{a_L}^{-1}$，二者相乘为恒等。证毕。

在同一允许字母表的 FIB 未读门字中，得到 $9L$ 的逆实现上界。这不撤销中途测量、旧隐藏标签或完整路径记录；原文后续章节正研究这些恢复障碍。

原生原子性也不等于正交切向。若 $\ker\mathcal P_j$ 与 $\operatorname{ran}\mathcal P_j$ 都非零，取其中的单位向量 $u,v$。输入 $(u+v)/\sqrt2$ 去除共同相位后沿

$$
\psi(t)=\frac{u+e^{i\alpha t}v}{\sqrt2},\qquad \alpha=3\pi/5
$$

运动。对应 Bloch 向量为 $\mathbf r(t)=(\cos\alpha t,\sin\alpha t,0)$。故

$$
\dot{\mathbf r}(0)\cdot\dot{\mathbf r}(1)
=\alpha^2\cos(3\pi/5)\ne0.
$$

项目的完整单脉冲并未要求两端切向正交。

### 8.2 另一固定菜单的非零等待没有精确有限逆

整体主文第 20 节的菜单另行固定：五模式 $U(s)=e^{-isK}$，只准 $s\ge0$ 等待、完整秩一模式读及 Stop；反馈树共同有限深度，没有额外量子旁路或存储 [1](#ref-omega)。对任意固定 $t>0$，目标是全输入上实现 $U(t)^\dagger$ 的通道；$t=0$ 的平凡恒等目标不在该障碍内。

其谱为

$$
\{0,\pm\omega_+,\pm\omega_-\},\qquad
\omega_\pm^2=\frac{5\pm\sqrt{17}}2,
$$

且

$$
\left(\frac{\omega_+}{\omega_-}\right)^2
=\frac{21+5\sqrt{17}}4
$$

无理。若仅等待 $T\ge0$ 就能实现该逆通道，则 $U(T+t)$ 为标量恒等；零本征值又使标量为一。因为 $T+t>0$，这要求两频率同时取得整周相位，迫使频率比有理，矛盾。

若含秩一读出，非零叶 Kraus 算子秩至多一；酉通道的非零 Kraus 算子必须与同一个满秩酉成比例。所以读出反馈也不能在该菜单中给出全输入的精确确定性有限逆。这不排除近似回返，恰与定理 7.1 相容。

#### 定义 8.2（逆实现的内部控制成本）

给原生权重 $w(a)>0$，定义

$$
C^-_\varepsilon(U)=
\inf\left\{
\sum_{a\ \mathrm{in}\ v}w(a):
v\ \mathrm{合法},\
\lVert\operatorname{Exec}(v)-U^\dagger\rVert_{\rm op}\le\varepsilon
\right\},
$$

空集合的下确界为 $+\infty$。权重表示调用数、内部时间还是另一种资源，必须明确标定。

这种成本刻画“能否造出逆门及代价”，一般不等于 Hamiltonian 能量。

**白话图景。**项目中确实有只能正向调用、却能用九次调用拼出逆门的原子。也确实有另一个菜单，只向前等待再加测量仍不能精确拼出逆门。差别在频谱和控制权限，而不在有没有给它叫作“能量”或“手性”。

<a id="section-10"></a>

## 9. 更大结构：增长历史之上出现可逆执行闭包

#### 定理 9.1（正词执行闭包是紧群）

设 $\mathcal S_+\subset U(d)$ 是原生正词的执行幺半群，含空字 $I$。则其算子范数闭包 $\overline{\mathcal S_+}$ 是 $U(d)$ 的紧子群。

**证明。**有限维 $U(d)$ 紧，闭子集仍紧。乘法连续使闭包对乘法封闭。任取 $V$ 在闭包中，其所有正幂也在闭包中。由定理 7.1，存在正幂 $V^{n_k-1}\to V^\dagger$，所以 $V^\dagger$ 也在闭包内。证毕。

因此有三层结构：

$$
\Sigma_+^*
\xrightarrow{\operatorname{Exec}}
\mathcal S_+
\subset
\overline{\mathcal S_+}\le U(d).
$$

第一层保留历史长度，第二层记录精确执行，第三层记录可任意逼近的执行。第三层有逆，不意味着第二层总有有限逆字，也不意味着第一层发生事件删除。若所有原子都有有限阶，第二层已经是群，第一层仍是正词历史。

复手性与控制单向性也要区分。$U$ 与 $U^\dagger$ 都满足

$$
UJ=JU,\qquad U^\dagger J=JU^\dagger,
$$

并保持同一个 $g,\omega$。固定 J 不会自动禁止数学逆。哪些方向可直接调用，由合法菜单规定。

**白话图景。**底下是一份只会增加的过程记录；中间是这些过程在工作内容上实际做了什么；再往上是它们能够任意逼近的关系。下面可以单向增长，上面的关系却可以形成群。这就是回溯与整体可逆性能够同时放在 $\Omega$ 内，而不需要外部倒拨历史的原因。

<a id="section-11"></a>

## 10. 有向回路留下什么：继承的接触相位而非最小面积

V74 已给归一二元旋量上的连接 [2](#ref-v74)

$$
\alpha=-i\langle\psi,d\psi\rangle,\qquad
d\alpha(u,v)=2\operatorname{Im}\langle u,v\rangle=\omega(u,v)/\hbar.
$$

对水平场 $X,Y$，外微分恒等式给

$$
\alpha([X,Y])=-d\alpha(X,Y).
$$

局部可写为

$$
\alpha=dz-x\,dy,\qquad
X=\partial_x,\qquad Y=\partial_y+x\partial_z,\qquad [X,Y]=\partial_z.
$$

沿水平路径 $\dot z=x\dot y$。顺次执行 $X:a, Y:b, X:-a, Y:-b$，只要全程留在该图中，

$$
\Delta x=\Delta y=0,\qquad\boxed{\Delta z=ab.}
$$

两段 Y 的贡献分别为 $(x+a)b$ 和 $-xb$，相加即得。这给二元变化顺序产生第三个相位关系的精确模型。

#### 命题 10.1（完整逆抵消与底面闭路不同）

若整个算子字真为 $U^{-1}U$，则它在所含全部相位与参照上为恒等。若只要求底面读出 $(x,y)$ 返回，则上面的 $z$ 可以留下非零相位。

**证明。**第一句是完整算子逆的定义。第二句由上述水平矩形直接给出。证毕。

所以不能同时称一个过程为“完整门与其精确逆”，又要求它在同一完整对象上必然留下无法抵消的相位。留下相位意味着恢复目标只覆盖了部分读出，或走的是不同续接。

符号沿用 V74：局部截面 $\mathcal A=-x\,dy$，顺序 Bargmann 乘积的细分闭路相位为 $+\oint\mathcal A=-ab$，水平提升相位为 $-\oint\mathcal A=+ab$。有限四角点乘积一般不等于实际整条矩形路径的精确面积相位。该坐标控制图也不自动给所有未知输入上的同一个线性门。

**白话图景。**绕一圈可以让底下两个读数回到原位，同时让相对于内部参照的相位多转一点。这个剩余量记住的是两种变化的先后关系。它可以任意小；有方向的面积并没有自动变成不可分的小块。

<a id="section-12"></a>

## 11. 椭圆的充分条件与反例

### 11.1 连严格同手性弯曲也不足以推出椭圆

#### 命题 11.1（光滑、严格正曲率而非椭圆的闭路）

取 $0<\varepsilon<1/12$，令

$$
r(\theta)=1+\varepsilon\cos3\theta,\qquad
\gamma(\theta)=r(\theta)(\cos\theta,\sin\theta).
$$

它简单闭合、始终正向且曲率处处为正，但不是椭圆。

**证明。**$r>0$，故曲线为正的径向图，简单且正则，$\det(\gamma,\gamma')=r^2>0$。曲率分子为

$$
r^2+2(r')^2-rr''
\ge(1-\varepsilon)^2-9\varepsilon(1+\varepsilon)
=1-11\varepsilon-8\varepsilon^2>1/36>0.
$$

该曲线具有三重旋转对称，且半径不恒定。若它是椭圆，其中心必须为旋转固定点，定义椭圆的正二次型必须与 $120^\circ$ 旋转对易；二维实对称矩阵满足此条件时只能为标量，因而只能是圆，矛盾。证毕。

### 11.2 正二次型与面积关系精确给出椭圆

这里 $z=(q,p)^{\mathsf T}$ 是一个已声明、单位相容的二维读出或相空间坐标，不直接等于归一 Hilbert 态的两个幅度。令

$$
\Pi=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
\omega_{\rm pl}(u,v)=u^{\mathsf T}\Pi v,\qquad
E(z)=\tfrac12z^{\mathsf T}Qz,\qquad Q=Q^{\mathsf T}>0.
$$

$\Pi$ 是本段的 Poisson 矩阵，不与前述复乘法 $J$ 混记。给定手性 $\sigma\in\{+1,-1\}$，要求对任意第二方向 $y$ 有

$$
\omega_{\rm pl}(\dot z,y)=\sigma\,dE_z(y).
$$

由于面积形式非退化，它唯一给出

$$
\boxed{\dot z=\sigma\Pi Qz.}
$$

这是在明确附加模型条件下得到的推论，不是本轮的第二个普遍公理。

#### 定理 11.2（稳定二次流的形状、周期与面积）

令 $A=\sigma\Pi Q$、$\nu=\sqrt{\det Q}>0$。则

$$
A^2=-\nu^2I,\qquad
\Phi_t=\cos(\nu t)I+\frac{\sin(\nu t)}\nu A.
$$

每个非零轨道完整遍历 $z^{\mathsf T}Qz=2E>0$ 的椭圆，最小周期为 $T=2\pi/\nu$。若 Q 的本征值为 $\lambda_1,\lambda_2$，半轴为

$$
a=\sqrt{2E/\lambda_1},\qquad b=\sqrt{2E/\lambda_2}.
$$

非零轨迹为圆当且仅当 $Q=qI$。

**证明。**写 $Q=\begin{psmallmatrix}a_0&c\\c&b_0\end{psmallmatrix}$，直接相乘得 $(\Pi Q)^2=(c^2-a_0b_0)I$。指数级数分开奇偶次即得流公式。由 $A^{\mathsf T}Q+QA=0$ 得能量守恒。正交对角化 Q 给半轴；非零 $z$ 与 $Az$ 实线性无关，因为 $A^2=-\nu^2I$，故轨道完整绕行且首个正周期为 $2\pi/\nu$。证毕。

令 $y=Q^{1/2}z$，则

$$
\lVert y\rVert^2=2E,\qquad \dot y=\sigma\nu\Pi y.
$$

因此椭圆在能量所定的度量中是圆；在另一个读出尺度中呈椭圆。手性只改绕行方向，不改轨迹集合。

有向扫面积速率与整圈面积为

$$
\frac12\omega_{\rm pl}(z,\dot z)=-\sigma E,
\qquad \mathcal A=\pi ab=\frac{2\pi E}{\nu}=ET.
$$

这是“能量与面积变化率”在稳定二次模型中的精确关系。它仍没有最小正面积，因为 $E\downarrow0$ 时 $\mathcal A\downarrow0$。

**白话图景。**只说向同一边转，还没有规定各处要弯多少。正二次响应把这些变化连成一个整体：两个方向同样硬，就是圆；两个方向的响应不同，就是椭圆。手性决定顺时针还是逆时针，形状由响应各向异性决定。

<a id="section-13"></a>

## 12. 几种椭圆必须保留各自的来源

### 12.1 恒定量子比特生成元的球面轨道仍是圆

设

$$
H=h_0I+\frac{\hbar}{2}\boldsymbol\Omega\cdot\boldsymbol\sigma.
$$

Pauli 对易关系给

$$
\dot{\mathbf r}=\boldsymbol\Omega\times\mathbf r.
$$

若 $\boldsymbol\Omega\ne0$，取 $\mathbf n=\boldsymbol\Omega/\lVert\boldsymbol\Omega\rVert$，则 $\lVert\mathbf r\rVert=1$ 与 $\mathbf n\cdot\mathbf r=c$ 都保持。轨道为球面与平面的交圆，或极点处的固定点。反向控制只改变绕行方向。

#### 命题 12.1（球面圆的投影椭圆）

半径 $R$、所在平面单位法向为 $n$ 的圆，正交投影到单位法向为 $m$ 的平面时，半轴为

$$
R,\qquad R|\mathbf n\cdot\mathbf m|.
$$

**证明。**两平面相交方向的投影长度保持；圆平面内与之正交的方向投影缩放 $|\mathbf n\cdot\mathbf m|$。平行平面的情形由连续性或直接计算得到。

因此投影通常为椭圆；两平面互相垂直，即 $\mathbf n\cdot\mathbf m=0$ 时退化为线段。它不是球面轨道本身变成欧氏椭圆。

### 12.2 项目已有的分支椭圆预算

沿用 V80 已声明的圆形输入 [3](#ref-v80)

$$
x(t)=u\cos t+v\sin t,\qquad
\lVert u\rVert=\lVert v\rVert=1,\quad \operatorname{Re}\langle u,v\rangle=0.
$$

完整等距输出仍为圆。固定事件的未归一幅度

$$
y_e(t)=M_eu\cos t+M_ev\sin t
$$

是某个实线性映射对单位圆的像，故为椭圆、线段或点。形状矩阵为

$$
G_e=\begin{pmatrix}
\langle u,E_eu\rangle&\operatorname{Re}\langle u,E_ev\rangle\\
\operatorname{Re}\langle u,E_ev\rangle&\langle v,E_ev\rangle
\end{pmatrix},
\qquad E_e=M_e^\dagger M_e,
$$

并满足

$$
\boxed{0\le G_e\le I_2,\qquad\sum_eG_e=I_2.}
$$

**证明。**对 $(a,b)\in\mathbb R^2$，二次型等于 $\lVert M_e(au+bv)\rVert^2$。效果正性及完备性分别给上下界和求和恒等式。对 $G_e$ 作实正交对角化，其本征值平方根就是两半轴。

条件归一后的 $y_e(t)/\lVert y_e(t)\rVert$ 还多了一步非线性操作，不自动是同一条欧氏椭圆。

| 椭圆类型 | 充分结构 | 不应混同的量 |
| --- | --- | --- |
| 能量轮廓椭圆 | 二维正定二次能量与面积形式 | 相空间坐标不等于态幅度 |
| 观察投影椭圆 | 圆所在平面与读出平面不平行 | 投影不是原球面轨道 |
| 事件幅度椭圆 | 固定线性分支作用于已给圆 | 未归一幅度不等于条件态 |
| 协方差椭圆 | 二元读出协方差正矩阵 | 不确定性区域不等于运动轨迹 |

**白话图景。**同样看见椭圆，可能是运动本身的能量轮廓，也可能是从斜面看一个圆，还可能是某个结果分支对两个方向接收得不一样。把形状矩阵写出来，就能知道是哪一种关系造成的椭圆，而不需要把它们都归给回溯。

<a id="section-14"></a>

## 13. 最接近“不可压缩面积”的量子结论

#### 定理 13.1（协方差椭圆的二元正性下界）

令 $A,B$ 自伴，$\psi$ 归一，相关乘积与方差有定义。设

$$
u=(A-\langle\psi,A\psi\rangle)\psi,\qquad
v=(B-\langle\psi,B\psi\rangle)\psi,
$$

$$
C=\operatorname{Re}\langle u,v\rangle,\qquad
D_{AB}=\operatorname{Im}\langle u,v\rangle.
$$

则协方差矩阵

$$
\Sigma=\begin{pmatrix}(\Delta A)^2&C\\C&(\Delta B)^2\end{pmatrix}
$$

满足

$$
\boxed{\det\Sigma\ge D_{AB}^2
=\tfrac14|\langle\psi,[A,B]\psi\rangle|^2.}
$$

**证明。**两个向量 $u,v$ 的复 Gram 行列式非负；交叉项为 $C+iD_{AB}$，展开即得。

若在声明的共同定义域上另有 $[Q,P]=i\hbar I$，则

$$
\det\Sigma\ge\hbar^2/4.
$$

定义协方差椭圆为 $z^{\mathsf T}\Sigma^{-1}z\le1$，其面积满足

$$
\boxed{\operatorname{Area}(\mathcal E_\Sigma)=\pi\sqrt{\det\Sigma}
\ge\pi\hbar/2.}
$$

该系数对应此处选择的单位椭圆定义，不是每一步门必须扫过的面积。它约束同一态的两项共轭读出关系，不能推出任意两个正交切向都有同样下界。

有限维完整载体中，精确 $[Q,P]=i\hbar I$ 不成立：取迹左侧为零，右侧为 $i\hbar d\ne0$。有限三维关系提升可以承载局部协方差数据，不意味着一个完整有限矩阵模型已经容纳全局精确正则对易关系。

**白话图景。**量子理论里确实有一种不能同时压扁的二元面积：一对指定共轭读出的不确定性椭圆。它的下界来自对易关系和物理尺度，且描述同一态的读出分散。它不同于微积分小面积，也不同于一次原子门在轨迹上跨出的面积。

<a id="section-15"></a>

## 14. 能量、逆门成本与内生时钟

#### 定理 14.1（能量方差给射线速度与时间作用下界）

在有限载体上，设 $\psi$ 为 $C^1$ 归一曲线，$H(t)$ 自伴，且 $i\hbar\dot\psi=H(t)\psi$，取水平速度 $\xi=(I-\ket\psi\bra\psi)\dot\psi$。则

$$
\xi=-\frac{i}{\hbar}(H-\langle H\rangle)\psi,
\qquad\boxed{\lVert\xi\rVert=\Delta H/\hbar.}
$$

采用 $d_{\rm FS}([\psi],[\phi])=\arccos|\langle\psi,\phi\rangle|$ 的标度，

$$
\boxed{\int_0^T\Delta H(t)\,dt
\ge\hbar\,\arccos|\langle\psi(0),\psi(T)\rangle|.}
$$

**证明。**水平投影给第一式，取范数得到第二式；曲线长度不小于同一度量下端点距离，给最后一式。

若端态正交，右侧为 $\pi\hbar/2$；若 $\Delta H$ 恒定且非零，$T\ge\pi\hbar/(2\Delta H)$。这是 Anandan--Aharonov 几何关系在此标度下的形式，也是 V74 的已供接口 [2](#ref-v74)。端态正交不能替换成切向正交。

#### 命题 14.2（有限门甚至不能唯一决定能量生成元）

若 $U=\sum_j e^{i\theta_j}P_j$，给定时长 $\tau>0$，则

$$
H_{\mathbf m}=-\frac{\hbar}{\tau}
\sum_j(\theta_j+2\pi m_j)P_j,\qquad m_j\in\mathbb Z
$$

都满足 $e^{-iH_{\mathbf m}\tau/\hbar}=U$。

**证明。**在每个谱子空间逐项取指数；整数整周相位为一。

这些生成元可有不同能隙与中途切向，却有同一个完整有限门及同一个逆门。所以逆门可构建性不能一般定义标准 Hamiltonian 能量。仅在射线层，$H\mapsto H+cI$ 还不改变射线轨迹；保留内部相位参照时应明确追踪该共同相位。

时间重标 $\tau=f(t)$、$f'>0$ 给

$$
H_\tau=\frac{dt}{d\tau}H_t.
$$

因此路径形状、时钟速率与能量标度需要一起保留。本体静态时，令 $\Omega$ 在下式中特指整体在该载体上的固定归一向量表示，取可微酉的内部移动参考 $R(t)$，则

$$
\psi=R^\dagger\Omega,\qquad
H_{\rm rel}=-i\hbar R^\dagger\dot R.
$$

这只用内部参照关系表示观察到的运动，不引入外部时间机器。

**白话图景。**能量可以驱动实现逆门，但“有没有逆路线”首先是控制菜单的问题。能量更直接的作用，是决定内容相对于内部时钟改变得多快；在态空间中，对应速度的是能量方差。同一个有限门可以有不同能量历程，所以还需要保留实现时间和中途关系。

<a id="section-16"></a>

## 15. 由本轮候选完整接回有限维量子规则

本节明确给依赖，沿用已建立的共同核、读出、记录与组合接口，不把一条新回返条件宣称为全部静态结构的唯一来源。

#### 定理 15.1（共同正核给 Hilbert 表示）

对内容集合上的归一复正核 $k$，在形式有限和上定义

$$
\left\langle\sum_i c_i\delta_{x_i},
\sum_jd_j\delta_{y_j}\right\rangle
=\sum_{i,j}\bar c_i k(x_i,y_j)d_j.
$$

商去零范数方向得到内积空间。有限秩切口给有限维复 Hilbert 空间 $H$，且 $k(x,y)=\langle\iota(x),\iota(y)\rangle$。

**证明。**所有有限 Gram 正性给半内积与 Cauchy--Schwarz。零范数向量与全部向量正交，故商内积良定义；有限维自动完备。

叠加的数学表示由张成得到，实际可准备组合仍由声明操作闭包供给。整体相位只在没有可访问相对参照时商成射线。

#### 定理 15.2（闭合门、生成元及记录仪器）

$C_{84}$ 给实际酉门 $U$。若门族可微，令 $K=\dot UU^\dagger$、$H=i\hbar K$，则

$$
K^\dagger=-K,\qquad H^\dagger=H,\qquad i\hbar\dot\psi=H\psi.
$$

对内部记录准备 $\ket0$、记录基 $\ket e$，定义

$$
M_e=(I\otimes\bra e)U(I\otimes\ket0).
$$

则

$$
\sum_eM_e^\dagger M_e=I,\qquad
E_e=M_e^\dagger M_e,\qquad
p(e|\psi)=\lVert M_e\psi\rVert^2
=\langle\psi,E_e\psi\rangle
$$

在既有同根强度标定下成立。

**证明。**主定理给 $U$；微分 $UU^\dagger=I$ 得生成元的反自伴性。记录基完备给 Kraus 完备式；其余由效果定义与已声明概率标定。

非零结果的条件后继是 $M_e\psi/\lVert M_e\psi\rVert$。合并或不读内部记录标签，得到相应 Kraus 完全正仪器。这些式子的标准通道表述见 Watrous [7](#ref-watrous)。

#### 定理 15.3（全效果相容响应给密度矩阵）

在全部 $0\le E\le I$ 上给非负同一响应 $f$，要求 $f(I)=1$，并对合法和满足 $f(E+F)=f(E)+f(F)$。则存在唯一 $\rho\ge0$、$\operatorname{Tr}\rho=1$，使

$$
f(E)=\operatorname{Tr}(\rho E).
$$

**证明。**可加性先给有理齐次性，正性给单调性，有理上下夹逼给实齐次性。对 $A\ge0$ 取正整数 $n\ge\lVert A\rVert$，定义 $\ell(A)=nf(A/n)$；共同分割使之与 $n$ 无关且正锥可加。以自伴算子的正差延拓，再用有限维迹对偶得到唯一 $\rho$。正性与归一分别给 $\rho\ge0,\operatorname{Tr}\rho=1$。

#### 定理 15.4（乘积核与张成给复合系统）

若独立准备满足

$$
k_{AB}((x,y),(x',y'))=k_A(x,x')k_B(y,y'),
$$

且这些乘积准备张成声明复合载体，则

$$
H_{AB}\cong H_A\otimes H_B.
$$

**证明。**将乘积准备映到 $\iota_A(x)\otimes\iota_B(y)$，乘积核保证内积一致。商去零元得到等距，张成保证满射。

实际局部端口若为 $A\otimes I$、$I\otimes B$，它们对易。远端保持迹的完整仪器满足 $\sum_eM_e^\dagger M_e=I$，所以忽略其结果不会改变本端效果响应。

#### 命题 15.5（投影更新所需的额外条件）

若结果效果为投影 $P$，且该结果操作固定 $\operatorname{ran}P$ 内的每个纯态，则其未归一通道为 $\rho\mapsto P\rho P$。

**证明。**写 Kraus 算子 $A_\alpha$。$\sum_\alpha A_\alpha^\dagger A_\alpha=P$ 使 $A_\alpha=A_\alpha P$。固定每个范围内纯态使 $A_\alpha\psi$ 与 $\psi$ 共线。线性叠加比较给 $A_\alpha=c_\alpha P$；当 $P\ne0$ 时，效果等式再给 $\sum_\alpha|c_\alpha|^2=1$。$P=0$ 时所有 Kraus 算子为零。

效果 $P$ 单独还允许范围内部附加变化，所以不直接推出 Lüders 更新。

#### 定理 15.6（有限过程的条件重建）

在上述接口和 $C_{84}$ 下，由上述准备、门、记录读出及粗粒化生成的实际有限过程，具有标准复量子态、效果、酉门和完全正仪器表示。若准备与控制菜单供应全部相应数学对象，则得到整个有限维量子过程类；受限菜单只给其中的原生可实现子理论。

**证明。**前述定理给所有正向表示。反向，对任一满足 $\sum_\alpha M_\alpha^\dagger M_\alpha=I$ 的有限 Kraus 族，

$$
W\psi=\sum_\alpha M_\alpha\psi\otimes\ket\alpha
$$

由完备式为等距。在足够大的有限共同载体中补齐正交基，把它扩成酉门，再读内部记录即可实现原仪器。若只给保持迹不增的分支族，先补入 $\sqrt{I-\sum_\alpha M_\alpha^\dagger M_\alpha}$ 对应的剩余结果。任意效果可用 $\sqrt E,\sqrt{I-E}$ 两分支实现；任意密度矩阵有谱分解准备或纯化表示。有限酉门满足本轮的回返候选。这些数学实现不自动扩大一个事先受限的原生菜单。

| 标准规则 | 内部关系来源 | 保留的明确条件 |
| --- | --- | --- |
| 复 Hilbert 空间 | 共同正核的零范数商 | 共同复方向与有限秩切口 |
| 线性酉门 | N、$R_B^+$、J 的有限锚刚性 | 完整同维球面、全部输入比较 |
| 正向近似逆 | 有限谱相位共同回返 | 重复调用合法、精度明确 |
| 精确原生逆 | 原生周期或其他正词关系 | 不把闭包误作有限词 |
| 薛定谔方程 | 可微酉族的切向生成元 | 实际时钟及物理单位 |
| 效果与 Born 规则 | 记录分支及强度校准 | 可读接口与同根概率标定 |
| 密度矩阵 | 全效果的正归一部分可加响应 | 全效果拓展兼容 |
| 张量积与纠缠 | 乘积核、张成及相干组合 | 复合端口与控制供应 |
| 投影更新 | 投影效果与确定子空间无扰动 | 非零结果条件化 |
| 不确定性 | 同一二元水平 Gram 正性 | 共轭结构及共同定义域 |
| 周期与椭圆 | 谱相位、正二次型或线性读出 | 分清实际轨迹和观察投影 |

**白话图景。**共同核说明内容怎样比较，正历史回返把完整门锁成酉变化，可微极限给生成元与薛定谔方程。内部记录把完整变化拆成效果、概率和条件后继；全效果相容性给密度矩阵，乘积关系给复合系统。这是一套可以逐项检查依赖的有限量子理论，不靠把所有前提藏进“内生”一个词中。

<a id="section-17"></a>

## 16. 一段白话与本轮结论边界

**白话图景。**$\Omega$ 中既有内容，也有它怎样被读出、怎样继续变化、怎样留下记录的关系。观察者沿原生允许方向不断增加门序列。一次逆作用也能由更多正向调用拼出来，所以工作内容看起来退回，历史仍在前进。如果一个完整门不扩大二元差别，并能靠正向重复让有限组正反参照共同回近原位，它就不能把这些差别偷偷压掉；所有方向被锁住后，门被迫成为酉门。正交和手性给出有向的二元比较框，却没有自动给最小面积。绕圈可以留下相对于内部参照的相位，能量方差决定沿态空间走得多快。圆或椭圆取决于实际生成元及读出响应：方向尺度相同会是圆，稳定二次响应不等会是椭圆，斜向观察或选择一个分支也能看见椭圆。逆门能否精确造出来取决于原生回返关系，不能单由“有能量”或“有手性”决定。

本轮严格新增的是有限锚定正回返与实际酉性之间的连接，以及它对原生逆实现的用途。正交面积、接触相位、量子回返、能量速度和量子仪器的既有数学归属均明确保留。候选与有限维酉门在声明背景内等价，不宣称仅由“一切属于 $\Omega$”就唯一推出全部物理规律。全局无限体系、具体 Hamiltonian、原生代价权重以及实验常数，仍需要其对应的内部接口。

本文没有修改远端仓库，也没有把未核读的新提交作为证据。

## 来源与版本关系

<a id="ref-omega"></a>

1. trureturing，[*整体静态相容纤维理论固定原文*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，本轮核读第 3--4、7、20 节：正历史、执行商、历史移位和固定菜单逆障碍。

<a id="ref-fibv"></a>

2. trureturing，[*AURIC 量子原则与相干重建续卷 V 固定原文*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md)，第 1 节：完整正向单位脉冲与 $K_j^{10}=I$。

<a id="ref-v74"></a>

3. trureturing，[*V74 平滑量子历史、余切动力学与内生运动固定原文*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)，第 4、5、8、9、10 节。

<a id="ref-v80"></a>

4. trureturing，[*V80 全结果二元差分不增、有限定向锚与内生量子过程固定原文*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)，第 3--5、8 节。

<a id="ref-v83"></a>

5. 本对话连续研究，[AURIC v83：反向内容完备与内部回返](https://chatgpt.com/library?file_id=libfile_15dee9b9be9081918ee9314f6e95346c&account_id=personal)，2026 年 11 月 2 日。

<a id="ref-wallace"></a>

6. David Wallace, *Recurrence Theorems: a unified account*, Journal of Mathematical Physics **56**, 022105 (2015)。[arXiv:1306.3925](https://arxiv.org/pdf/1306.3925)；[DOI:10.1063/1.4907384](https://doi.org/10.1063/1.4907384)。本轮核读统一有限维回返相关定理。

<a id="ref-bocchieri"></a>

7. P. Bocchieri and A. Loinger, *Quantum Recurrence Theorem*, Physical Review **107**, 337--338 (1957)。[DOI:10.1103/PhysRev.107.337](https://doi.org/10.1103/PhysRev.107.337)。本轮核读出版信息与摘要；本文所需有限维证明独立写出。

<a id="ref-aa"></a>

8. J. Anandan and Y. Aharonov, *Geometry of quantum evolution*, Physical Review Letters **65**, 1697--1700 (1990)。[DOI:10.1103/PhysRevLett.65.1697](https://doi.org/10.1103/PhysRevLett.65.1697)。本轮核读官方摘要；速度公式在正文完整推导。

<a id="ref-watrous"></a>

9. John Watrous, *The Theory of Quantum Information*, [第 2 章作者公开稿](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。沿用前轮已核读的态、通道、Kraus 与仪器接口。

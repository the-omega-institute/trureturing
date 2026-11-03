# AURIC：刚性镜像、复相位与原生黄金门

**帽子铺砌的量子提升、28 次镜像编译与反手性障碍**

定义、定理与纸面证明

*v27.0 · 2026 年 10 月 30 日 · Asia/Singapore*

## 摘要

“允许旋转与镜像、禁止缩放”只有在明确其作用空间后才能成为量子命题。
本文区分欧氏铺砌坐标、复振幅空间、量子比特 Bloch 球与层级尺度，证明几何镜像可在配置编码中成为复线性酉操作，
而普遍未知振幅共轭是另一种不满足完全正性的任务。
在项目原生十三维扇区中，构造左右地址反序  $S$ ，证明  $SK_ jS^\dagger=K_ {6-j}$ ；
进一步以 Garside 半扭转给出精确到整体相位、仅含 28 次正向原生调用的实现。
对任意已知门字，逐调用用  $K_ j^9$  替换可精确编译其复共轭矩阵，但与反转执行次序的逆电路不同。
另一方面，边界门的  $8+5$  本征重数分裂排除固定酉换框到其逆，并给出精确算子范数间隙  $2\sin(3\pi/20)$ 。
对于非正交的三通道或五读出编码，给出完整 Gram 矩阵与非零重叠闭环的酉提升充要条件；
三态例子直接展示两两转移概率遗漏的相位手性。
最后自足证明普遍转置的最优信道保真度  $2/(d+1)$ ，并把共同换框、真实操作、时钟边权和观测菜单分别放回静态关系图。
所得理论为用户的镜像直觉提供可执行的原生构造与可检验的判据；它没有把铺砌刚性本身当作全部量子公理的推导。

**方法与来源身份。**
所有数学计算均为纸面符号推导；未运行数值实验、CAS、数学枚举、门字搜索或 Lean。
检索、源码比对、排版编译与页面检查只用于核对来源及交付。
Wigner 对称、Householder 变换、Garside 半扭转、Gram 判据和最优转置均有既有数学背景。
本文的增量是把它们接到指定 AURIC 操作模型，给出明确构造与边界，不主张这些一般工具的原创优先权。


---

**来源身份与范围。** 本卷是指定 XeLaTeX 源码的忠实 Markdown 转换；固定项目快照为 `66259f03d60716f143cd59c7644dadcb67cc1b73`。数学计算仍是纸面符号推导；源码比对、排版转换、文本/哈希/渲染检查只核对交付，不构成新的数学或 GitHub 托管渲染认证。

## 目录

- [1. 固定快照、最新进展与研究目标](#section-1)
- [2. 刚性发生在哪一个空间](#section-2)
- [3. 帽子镜像的量子提升与它没有自动供应的结构](#section-3)
- [4. 黄金门中的反射与相位：继承并核对项目结果](#section-4)
- [5. 原生空间镜像与二十八次精确编译](#sec:28)
- [6. 镜像程序、逆程序与内生读出的共同换框](#section-6)
- [7. 十三维反手性换框的精确障碍与扩充方式](#sec:gap)
- [8. 非正交读出的酉镜像：完整 Gram 与闭环判据](#sec:gram)
- [9. 真正的 Bloch 镜像为何需要噪声：完全正性与最优界](#sec:transpose)
- [10. 静态关系中的观察者：共同换框、真实菜单与最新时钟](#sec:latest)
- [11. 面向 AURIC 五模式的建设性研究形式](#section-11)

<a id="section-1"></a>

## 1. 固定快照、最新进展与研究目标

本轮固定的 `dev` 提交为
`66259f03d60716f143cd59c7644dadcb67cc1b73`。
提交时间为 2026 年 10 月 30 日 18:26:54（新加坡；UTC 10:26:54），合并 PR #24158。
相对 v26 的 `e3391e9` 前进 9 个提交；完整比较有 180 个变更文件，其中 theory 目录有三个。
相干重构续卷 II、黄金门 v15 和铺砌 v23 的 Git blob 均未变化；量子主线仍到第 95 节。
因此，本轮不能把新推导写成“仓库已经新增了这些量子定理”。[\[1\]](#bib-repohead) [\[3\]](#bib-repoborn) [\[2\]](#bib-repov15) [\[4\]](#bib-repov23)

三个实际理论增量分别是：自标定关系数学 IV 第 21 节的四维同容限覆盖障碍；
周期时钟刚性第 17--21 节的真实子节点传递、暂态依赖和实际时钟像；
不等长蜘蛛图幂的零强制结果。
前两项与观察者、尺度和静态图的接口相关；第三项不被借用为量子镜像的证据。
本稿第 [10](#sec:latest) 节给出前两项的适用范围。[\[7\]](#bib-repoself) [\[8\]](#bib-repoclock) [\[9\]](#bib-repospider)

统一记号为

<a id="eq-eq:constants"></a>

```math
\varphi=\frac{1+\sqrt5}{2},\qquad x=\varphi^{-1},\qquad
 y=\sqrt x,\qquad \zeta=e^{3\pi i/5},\qquad \theta=\frac{3\pi}{5}.\tag{1}
```

于是  $x+x^2=1$ 、 $\zeta^5=-1$ 、 $\zeta+\zeta^{-1}=-x$ 。
内积对第一变量共轭线性、对第二变量线性。 $A^\dagger$  表示伴随，
 $\overline A$  表示在固定基中的逐项复共轭， $A^{\mathsf T}$  表示转置。
这三个操作不能互换。


| 所说的“镜像” | 精确定义 | 与标准量子门的关系 |
|---|---|---|
| 配置左右反序 |  $\lvert T\rangle\mapsto\lvert mT\rangle$  | 配置集合对镜像封闭时，是置换酉门 |
| 投影子空间反射 |  $R_ P=2P-I$  | 复线性厄米酉对合；原生  $K^5$  即此类 |
| 未知振幅共轭 |  $\psi\mapsto\overline\psi$  | 反酉；不能成为普遍确定性局部信道 |
| Bloch 球平面镜像 |  $\mathbf r\mapsto O\mathbf r$ ,  $\det O=-1$  | 对应反酉射线对称；不是酉共轭 |
| 已知电路镜像编译 |  $K_ p\mapsto\overline{K_ p}$  | 对程序做替换，可由普通酉门执行 |


<a id="section-2"></a>

## 2. 刚性发生在哪一个空间


<a id="stmt-2-1"></a>

#### 定义 2.1：三个载体

铺砌坐标属于欧氏平面  $E=\mathbb R^2$ ，其刚体变换为  $q\mapsto Rq+t$ ， $R\in O(2)$ 。
量子振幅属于复希尔伯特空间  $H$ ，闭系统门通常取复线性酉算子。
量子比特的密度算子写作  $\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2$ ，
 $\mathbf r$  属于实三维 Bloch 球。三个空间中的距离、定向与镜面不是同一个对象。


<a id="stmt-2-2"></a>

#### 定理 2.2：保持范数需要与复线性共同陈述

有限维复线性映射  $U:H\to H$  保持每个向量的范数，当且仅当  $U^\dagger U=I$ 。
因此它不能把全部向量统一乘以模长不为一的因子。


**证明。**

令  $A=U^\dagger U-I$ 。范数保持给  $\langle v,Av\rangle=0$  对每个  $v$  成立。
将  $v$  依次取为正交基向量、两个基向量之和及带  $i$  的和，分别得到所有对角、实非对角、虚非对角元为零。
故  $A=0$ ；有限同维下等距映射也是满射。反向直接由内积公式成立。
若  $U=cI$ ，则  $U^\dagger U=|c|^2I$ ，所以必须  $|c|=1$ 。

**证毕。**

> **编者条件说明（保留上述原文）。** 关于标量门的推论 $|c|=1$ 使用 $H\ne\lbrace 0\rbrace$，以便选取非零向量；零维时 $U^\dagger U=I$ 的等价式仍成立，但 $cI$ 不限制 $c$ 的模长。


<a id="stmt-2-3"></a>

#### 命题 2.3：复结构与实刚性

把  $z=a+ib\in\mathbb C^d$  写为  $(a,b)\in\mathbb R^{2d}$ ，令

```math
J_0=\begin{pmatrix}0&-I\\I&0\end{pmatrix},\qquad
 \mathcal R(A+iB)=\begin{pmatrix}A&-B\\B&A\end{pmatrix}.
```

实算子  $T$  对应复酉算子，当且仅当  $T$  正交且  $TJ_ 0=J_ 0T$ 。
对应反酉算子，当且仅当  $T$  正交且  $TJ_ 0=-J_ 0T$ 。
对任意  $U\in U(d)$ ，

```math
\det_{\mathbb R}\mathcal R(U)=|\det_{\mathbb C}U|^2=1.
```

反酉算子的实行列式则为  $(-1)^d$ 。


**证明。**

与  $J_ 0$  对易恰好表示保持乘以  $i$  的运算，解分块等式即得显示的实化形式。
实与复范数相同，故正交性对应酉性。
共轭  $C(a,b)=(a,-b)$  反对易于  $J_ 0$ ；任一反对易正交算子乘以  $C$  后变成对易正交算子。
在复数域上， $\mathcal R(U)$  相似于  $\operatorname{diag}(U,\overline U)$ ，所以有行列式公式。
最后  $\det_ \mathbb R C=(-1)^d$ ，乘以酉实化不改变它。

**证毕。**


这也说明，仅凭“实空间中保持定向”不能判断量子酉性： $d=2$  时反酉在  $\mathbb R^4$  中同样保持定向。
需要说明与哪一个复结构相容。Wigner 定理讨论保持全部射线转移概率的对称时出现酉／反酉两支；
它的前提是量子射线几何，不能只由一块帽子的欧氏全等替代。[\[13\]](#bib-wigner)


<a id="stmt-2-4"></a>

#### 定理 2.4：希尔伯特反射在 Bloch 球上是半周旋转

若  $P=(I+\mathbf n\cdot\boldsymbol\sigma)/2$  是量子比特的秩一投影， $|\mathbf n|=1$ ，
则  $R_ P=2P-I=\mathbf n\cdot\boldsymbol\sigma$  是酉门，其 Bloch 作用为

<a id="eq-eq:bloch-halfturn"></a>

```math
\mathbf r\longmapsto(2\mathbf n\mathbf n^{\mathsf T}-I)\mathbf r.\tag{2}
```

这是绕  $\mathbf n$  轴的  $\pi$  旋转，三维行列式为  $+1$ 。
反之，固定基共轭在 Bloch 球上给
 $(r_ x,r_ y,r_ z)\mapsto(r_ x,-r_ y,r_ z)$ ，行列式为  $-1$ 。


**证明。**

 $R_ P^2=I$ 。Pauli 乘法恒等式给
 $(\mathbf n\cdot\sigma)(\mathbf r\cdot\sigma)(\mathbf n\cdot\sigma) =[2\mathbf n(\mathbf n\cdot\mathbf r)-\mathbf r]\cdot\sigma$ 。
沿轴本征值为  $1$ ，垂直平面两个本征值为  $-1$ 。
共轭保持  $\sigma_ x,\sigma_ z$  而反转  $\sigma_ y$ ，故得后一公式。
一般酉共轭保持 Pauli 内积，且  $U(2)$  连通，所以其 Bloch 正交作用始终在  $SO(3)$  中。

**证毕。**


<a id="stmt-2-5"></a>

#### 命题 2.5：空间镜像与空间缩放都可有酉实现

在  $L^2(\mathbb R^2)$  上，对于  $R\in O(2)$ 、 $t\in\mathbb R^2$ 、 $s\gt 0$ ，定义

<a id="eq-eq:spatial"></a>

```math
(U_{R,t}\psi)(q)=\psi(R^{-1}(q-t)),\qquad
 (D_s\psi)(q)=s^{-1}\psi(q/s).\tag{3}
```

两者均为复线性酉算子；即使  $\det R=-1$ ，第一式也不共轭振幅。
在适当共同定义域上， $D_ s^\dagger Q D_ s=sQ$ 、 $D_ s^\dagger P D_ s=s^{-1}P$ 。


**证明。**

第一式变量替换的 Jacobian 绝对值为一。
第二式由  $q=su$  得
 $\int s^{-2}|\psi(q/s)|^2d^2q=\int|\psi(u)|^2d^2u$ ，且逆为  $D_ {1/s}$ 。
位置乘法和动量微分的共轭公式可在 Schwartz 函数上直接代入，再取相应闭包。

**证毕。**


因此，禁止的是固定态空间内的统一范数放大，空间坐标的压缩／展开并不因此被禁止。
帽子的单砖铺放用全等副本；层级重标尺讨论的是不同的几何映射。
前稿已区分 Hat 形状的  $\varphi^2$  扩张和数量的  $\varphi^4$  增长。
若一个有限维矩阵有本征值  $\varphi^2\gt 1$ ，它不可能关于任何正定内积成为酉算子：
对该本征向量  $v$ ，保持范数将要求  $\Vert v\Vert =\varphi^2\Vert v\Vert$ 。
这与式 [(3)](#eq-eq:spatial) 中带 Jacobian 的函数空间酉作用并不冲突。[\[10\]](#bib-hat) [\[11\]](#bib-cap)


<a id="section-3"></a>

## 3. 帽子镜像的量子提升与它没有自动供应的结构

原始 Hat 允许平移、旋转及反射的全等铺放，而且每个合法整平面铺砌均含两种手性的帽子。
Hat 占优的铺砌类经镜像进入 anti-Hat 占优类。
因此若要把镜像定义为同一配置空间中的作用，应选取对镜像封闭的配置集合，
或把两个镜像扇区一起保留。[\[10\]](#bib-hat) [\[11\]](#bib-cap)


<a id="stmt-3-1"></a>

#### 定义 3.1：配置编码

设  $\mathcal C$  为指定的合法带标签块或铺砌集合， $m:\mathcal C\to\mathcal C$  是双射且  $m^2=1$ 。
取  $H_ {\mathcal C}=\ell^2(\mathcal C)$ ，以配置  $T$  对应的  $\lvert T\rangle$  为正交基。
这是一个明确选择的量子编码；没有从几何标签自动推出配置必须正交。


<a id="stmt-3-2"></a>

#### 定理 3.2：刚体作用的配置酉提升

若几何作用  $g$  双射地作用于  $\mathcal C$ ，则

<a id="eq-eq:configurationlift"></a>

```math
U_g\lvert T\rangle=\lvert gT\rangle\tag{4}
```

唯一延拓成酉算子，并满足  $U_ gU_ h=U_ {gh}$ 。
特别地， $U_ m^2=I$ 、 $U_ m^\dagger=U_ m$ 。


**证明。**

正交基的置换保持所有有限线性组合的内积，因而连续延拓到完备化。
逆映射是  $U_ {g^{-1}}$ ；乘法关系在每个基矢上成立。

**证毕。**


该门的作用是  $\sum_ T c_ T\lvert T\rangle\mapsto\sum_ Tc_ T\lvert mT\rangle$ 。
反酉  $U_ mC$  则给  $\sum_ T\overline{c_ T}\lvert mT\rangle$ 。
它们在各个配置基矢上相同，在一般相干叠加上不同。
所以即使知道全部经典配置怎样镜像，也还没有确定相干振幅怎样变换。


<a id="stmt-3-3"></a>

#### 命题 3.3：只有配置置换与相位不能供应一般干涉

固定正交配置基上的置换与对角相位只生成单项酉矩阵。
若目标门把  $\lvert 0\rangle$  送到  $\lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$ ，则任一该类门  $M$  满足

<a id="eq-eq:monomialgap"></a>

```math
\inf_{|c|=1}\|M\lvert 0\rangle-c\lvert +\rangle\|\ge\sqrt{2-\sqrt2}.\tag{5}
```


**证明。**

单项矩阵的乘积仍为单项矩阵，所以  $M\lvert 0\rangle$  是某个基矢乘相位。
其与  $\lvert +\rangle$  的重叠模不超过  $1/\sqrt2$ 。
两个单位向量在允许整体相位后的最小距离平方为  $2-2|\langle u,v\rangle|$ ，得到结论。

**证毕。**


非周期性可以使配置集合丰富，仍不能代替相干混合矩阵。
AURIC 的非对角投影和复相位正是在这一步提供额外内容。
更一般的非正交编码需要第 [8](#sec:gram) 节的完整 Gram 判据。


<a id="section-4"></a>

## 4. 黄金门中的反射与相位：继承并核对项目结果

项目原生三位置矩阵为[\[2\]](#bib-repov15) [\[3\]](#bib-repoborn)

<a id="eq-eq:native"></a>

```math
Q=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix}
 =\begin{pmatrix}\sqrt x\\x\end{pmatrix}
   \begin{pmatrix}\sqrt x&x\end{pmatrix},\qquad
 \mathcal P=n_Ln_R+(1-n_L)(1-n_R)Q_C,
 \quad K=\zeta[I+(\zeta-1)\mathcal P].\tag{6}
```

因为  $x+x^2=1$ ， $Q$  是秩一投影；两个邻居控制条件互斥，故  $\mathcal P$  是实正交投影。
投影相位门的一般形式属于广义量子 Householder 变换的框架；其固定地址普适性仍需另外证明。[\[12\]](#bib-householder)


<a id="stmt-4-1"></a>

#### 命题 4.1：原生门的精确反射

对  $K_ P=\zeta[(I-P)+\zeta P]$ ，有

<a id="eq-eq:reflection"></a>

```math
K_P^m=\zeta^m(I-P)+\zeta^{2m}P,\qquad
 K_P^{10}=I,\qquad K_P^{-1}=K_P^9,\qquad K_P^5=2P-I.\tag{7}
```


**证明。**

 $P(I-P)=0$ ，两正交扇区上的幂分别计算。
代入  $\zeta^5=-1$  与  $\zeta^{10}=1$  即得。
 $2P-I$  自伴且平方为单位，所以严格酉。

**证毕。**


在五合法模式  $(000,100,010,001,101)$  上， $\mathcal P$  有一个秩一二维块与一个  $101$  分量，
故反射的正／负本征重数为  $2$  与  $3$ 。
它是子空间反射，而非五维实空间中的任意指定镜面；也不是对未知振幅做共轭。

项目 v15 的二维编码给  $P=\lvert 1\rangle\langle 1\rvert$  与式 [(6)](#eq-eq:native) 中的  $Q$ 。
下面结论在 v15 第 4--5 节已经证明；本稿重给短证明以说明相位的作用。


<a id="stmt-4-2"></a>

#### 定理 4.2：两个固定反射与完整黄金门的差别；继承结果

在上述同一实基中，

<a id="eq-eq:old-density"></a>

```math
\overline{\langle K_P^5,K_Q^5\rangle}=O(2),\qquad
 \overline{\{[W]:W\in\langle K_P,K_Q\rangle\}}=PU(2).\tag{8}
```

只保留反射时，到  $S_ 0=\operatorname{diag}(1,i)$  的精确射影距离为

<a id="eq-eq:old-gap"></a>

```math
\inf_{O\in O(2),|c|=1}\|O-cS_0\|_{\rm op}=\sqrt{2-\sqrt2}.\tag{9}
```


**证明。**

令  $R_ P=2P-I$ 、 $R_ Q=2Q-I$ 。
它们实正交，且
 $\operatorname{Tr}(R_ PR_ Q)=4\operatorname{Tr}(PQ)-2=4x^2-2=4-2\sqrt5$ 。
若乘积有限阶，其迹是互逆单位根之和，每个代数共轭都在  $[-2,2]$  中。
但另一个共轭为  $4+2\sqrt5\gt 2$ ，矛盾。
故乘积的幂在  $SO(2)$  中稠密，加一个反射给全部  $O(2)$ 。

把  $P$  换写成  $\operatorname{diag}(1,0)$ ，令
 

```math
J=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)
```

 。
完整门  $K_ P=\operatorname{diag}(\zeta^2,\zeta)$  将生成元  $J$  共轭为
 $\cos\theta J-i\sin\theta\sigma_ x$ ，与  $J$  实线性无关。
两者及其交换子张成  $\mathfrak{su}(2)$ ，所以闭包含  $SU(2)$ ，射影闭包即  $PU(2)$ 。
逆门由九次正向调用给出，未增加门类型。

最后  $O\lvert +\rangle$  为实单位向量，与  $S_ 0\lvert +\rangle=\lvert +i\rangle$  的重叠模恒为  $1/\sqrt2$ ，给式 [(9)](#eq-eq:old-gap) 下界。
取  $O=I,c=e^{-i\pi/4}$  时两个对角误差模均为该值，达到下界。

**证毕。**


此处重要的逻辑是：一个固定地址只有十个幂；两个相容而不交换的地址加上原生复相位，才产生全部单比特射影操作。
反射、旋转和不缩放的几何词汇不能代替对生成群的检验。


<a id="sec:28"></a>

## 5. 原生空间镜像与二十八次精确编译


<a id="stmt-5-1"></a>

#### 定义 5.1：原生十三维扇区

沿用项目第 77.1 节。十个站点为  $b_ {-1},b_ 0,\ldots,b_ 8$ ，
固定  $b_ {-1}=b_ 7=1$ 、 $b_ 0=b_ 6=b_ 8=0$ 。
令  $\beta=(b_ 1,\ldots,b_ 5)$  无相邻的  $1$ ，并置

<a id="eq-eq:13space"></a>

```math
e_\beta=\lvert 10\,\beta\,010\rangle,\qquad
 H=\operatorname{span}_{\mathbb C}\{e_\beta\},\qquad v=e_{00100}.\tag{10}
```

 $K_ j$  的中心为  $b_ j$ ， $0\le j\le6$ 。长度为  $n$  的合法串数满足
 $a_ n=a_ {n-1}+a_ {n-2}$ 、 $a_ 0=1,a_ 1=2$ ，故  $\dim H=a_ 5=13$ 。


项目第 77.2 节已经逐基建立此扇区与八个 Fibonacci 任意子总荷真空空间的对应，
再以 Jones--Wenzl 扇区的密度结果得到

<a id="eq-eq:project-density"></a>

```math
\overline{\{[K_p|_H]:p\text{ 为七地址有限正字}\}}=PU(H).\tag{11}
```

下文使用其中的编织关系与标量交换子代数；不从维数相同直接跳到密度。
该对应及外部密度前提的来源分别是项目第 77.2 节和 Freedman--Larsen--Wang 的 Theorem 0.1。
[\[3\]](#bib-repoborn) [\[15\]](#bib-flw)


<a id="stmt-5-2"></a>

#### 定理 5.2：原生左右反序

定义复线性算子

<a id="eq-eq:native-mirror"></a>

```math
S e_{\beta_1\cdots\beta_5}=e_{\beta_5\cdots\beta_1}.\tag{12}
```

则  $S=S^\dagger=S^{-1}$ ， $Sv=v$ ，而且

<a id="eq-eq:mirror-covariance"></a>

```math
S\mathcal P_jS^\dagger=\mathcal P_{6-j},\qquad
 SK_jS^\dagger=K_{6-j}\quad(0\le j\le6).\tag{13}
```


**证明。**

完整位置变化是  $b_ k\leftrightarrow b_ {6-k}$ （ $-1\le k\le7$ ），旁观位  $b_ 8$  固定。
它交换两端相同的固定边界，且反序不改变无相邻  $1$  的性质，因此是合法正交基的对合置换。
投影
 $\mathcal P_ j=n_ {j-1}n_ {j+1}+(1-n_ {j-1})(1-n_ {j+1})Q_ j$ 
对两个邻居对称，中心被送到  $6-j$ ，故逐项得到式 [(13)](#eq-eq:mirror-covariance)。
初态的中间串  $00100$  是回文，故保持。

**证毕。**


这个镜像保持同一个  $\zeta$ ，它改变空间地址，没有把每个门变成逆门。
接下来说明  $S$  不仅是一个形式上定义的酉矩阵，而且具有原生有限字实现。


<a id="stmt-5-3"></a>

#### 引理 5.3：Garside 半扭转的纯关系恒等式

设  $\sigma_ 1,\ldots,\sigma_ {n-1}$  满足远距交换和相邻编织关系。
令

```math
\Pi_n=\sigma_1\cdots\sigma_{n-1},\quad
 \Omega_n=\sigma_{n-1}\cdots\sigma_1,\quad
 \Delta_1=1,\quad \Delta_n=\Pi_n\Delta_{n-1}.
```

则

<a id="eq-eq:garside"></a>

```math
\Delta_n=\Delta_{n-1}\Omega_n,\qquad
 \Delta_n\sigma_j=\sigma_{n-j}\Delta_n\quad(1\le j<n).\tag{14}
```


**证明。**

对第一式归纳。用归纳假设和  $\sigma_ {n-1}$  与  $\Delta_ {n-2}$  中全部生成元交换，得

```math
\Pi_n\Delta_{n-1}
 =\Pi_{n-1}\sigma_{n-1}\Delta_{n-2}\Omega_{n-1}
 =\Delta_{n-1}\sigma_{n-1}\Omega_{n-1}
 =\Delta_{n-1}\Omega_n.
```

远距交换及一次相邻编织给滑移式

```math
\Pi_n\sigma_k=\sigma_{k+1}\Pi_n\quad(k\le n-2),\qquad
 \Omega_n\sigma_k=\sigma_{k-1}\Omega_n\quad(k\ge2).
```

例如第一式先把右端  $\sigma_ k$  移过  $\sigma_ {n-1},\ldots,\sigma_ {k+2}$ ，
把  $\sigma_ k\sigma_ {k+1}\sigma_ k$  改为  $\sigma_ {k+1}\sigma_ k\sigma_ {k+1}$ ，
再把最左的  $\sigma_ {k+1}$  移过  $\sigma_ {k-1},\ldots,\sigma_ 1$ 。
第二式反向同理。
当  $j\le n-2$ ，归纳得到
 $\Delta_ n\sigma_ j=\Pi_ n\sigma_ {n-1-j}\Delta_ {n-1} =\sigma_ {n-j}\Delta_ n$ 。
当  $j=n-1$ ，改用另一分解：
 $\Delta_ n\sigma_ {n-1}=\Delta_ {n-1}\sigma_ {n-2}\Omega_ n =\sigma_ 1\Delta_ n$ 。
初始  $n=2$  显然，归纳完成。

**证毕。**


这是标准 Garside 半扭转关系；上述证明只用群关系，便于直接移植到项目矩阵。
[\[14\]](#bib-garside)


<a id="stmt-5-4"></a>

#### 定理 5.4：二十八次正向原生调用精确实现空间镜像

在式 [(10)](#eq-eq:13space) 的整个  $H$  上，令

<a id="eq-eq:28word"></a>

```math
\Delta_K=(K_0K_1\cdots K_6)(K_0K_1\cdots K_5)
 \cdots(K_0K_1)K_0.\tag{15}
```

存在固定实数  $\chi$ ，使

<a id="eq-eq:28result"></a>

```math
\boxed{\Delta_K=e^{i\chi}S.}\tag{16}
```

算子乘积从最右边开始执行，总调用数为  $7+6+\cdots+1=28$ 。
该实现不用辅助位、中间测量或极限操作。


**证明。**

原生编织对应令  $\sigma_ i\mapsto K_ {i-1}$ 。
上一引理给
 $\Delta_ KK_ j\Delta_ K^\dagger=K_ {6-j}$ 。
与式 [(13)](#eq-eq:mirror-covariance) 比较， $S^\dagger\Delta_ K$  交换每个  $K_ j$ 。
它因而交换所有原生门字；式 [(11)](#eq-eq:project-density) 意味着它交换每个酉矩阵，
因为忽略整体相位不影响共轭作用。
有限维全矩阵代数的交换子只有标量：先与所有对角相位交换使其对角，再与基置换交换使各对角相等。
故  $S^\dagger\Delta_ K=e^{i\chi}I$ ，即得结论。

**证毕。**


该证明使用已有密度定理来确定交换子，但所得实现是一个固定有限字。
这里没有声称 28 是最短调用数； $\chi$  对未受控的态演化和通常测量不影响结果。
若把整段门字再作为受控分支，整体相位会变成分支间相对相位，需另行标定控制接口。


<!-- visible-square-start -->

```math
\begin{array}{ccc}
\boxed{\begin{array}{c}\psi\in H\\\text{原生输入}\end{array}}
& \xrightarrow{\ S\sim\Delta_K\ } &
\boxed{\begin{array}{c}S\psi\\\text{左右反序}\end{array}}\\[6pt]
{\scriptstyle K_j}\,\Big\downarrow && \Big\downarrow\,{\scriptstyle K_{6-j}}\\[6pt]
\boxed{\begin{array}{c}K_j\psi\\\text{地址 }j\text{ 的作用}\end{array}}
& \xrightarrow[\ S\sim\Delta_K\ ]{} &
\boxed{\begin{array}{c}K_{6-j}S\psi\\\text{镜像地址的作用}\end{array}}
\end{array}
```

<!-- visible-square-end -->

**图 1：** 同一个静态交换方块表示空间镜像的协变性。边上的矩阵相容有明确内容；不需要把方块解释为外部连续时间。

**排版说明。** 上方使用 Markdown `math` 围栏中的数组、方框与带标签箭头重画原图，保留四个节点的完整内容、原来的两行两列位置和两条有向路线。字体、颜色、圆角、线型、节点尺寸与间距不复现 TikZ 样式。

**原始 TikZ（逐字保留）：**

```tex
\begin{tikzpicture}[>=Stealth,node distance=12mm,
 box/.style={draw=blue!45!black,rounded corners,align=center,text width=48mm,minimum height=13mm,font=\small}]
\node[box] (a) {$\psi\in H$\\原生输入};
\node[box,right=24mm of a] (b) {$S\psi$\\左右反序};
\node[box,below=16mm of a] (c) {$K_j\psi$\\地址 $j$ 的作用};
\node[box,below=16mm of b] (d) {$K_{6-j}S\psi$\\镜像地址的作用};
\draw[->] (a)--node[above,font=\small]{$S\sim\Delta_K$} (b);
\draw[->] (a)--node[left,font=\small]{$K_j$}(c);
\draw[->] (b)--node[right,font=\small]{$K_{6-j}$}(d);
\draw[->] (c)--node[below,font=\small]{$S\sim\Delta_K$}(d);
\end{tikzpicture}
```


<a id="section-6"></a>

## 6. 镜像程序、逆程序与内生读出的共同换框


<a id="stmt-6-1"></a>

#### 定义 6.1：调用字与三种变换

令  $p=j_ 1\cdots j_ \ell$  按调用先后书写，项目约定
 $K_ p=K_ {j_ \ell}\cdots K_ {j_ 1}$ 。
空间镜像字  $s(p)$  逐地址替换  $j\mapsto6-j$ ；
复共轭编译字  $m(p)$  把每次地址  $j$  替为九次同地址调用并保留原调用次序；
逆程序则先逆转原调用次序，再以九次调用替代每个逆门。


<a id="stmt-6-2"></a>

#### 定理 6.2：已知电路的精确镜像编译

在合法计算基中，有

<a id="eq-eq:addressword"></a>

```math
\begin{aligned}K_{s(p)}&=SK_pS^\dagger,\end{aligned}\tag{17}
```

<a id="eq-eq:mirrorword"></a>

```math
\begin{aligned}K_{m(p)}&=\overline{K_p}
 =K_{j_\ell}^{-1}\cdots K_{j_1}^{-1},\end{aligned}\tag{18}
```

<a id="eq-eq:inverseword"></a>

```math
\begin{aligned}K_p^{-1}&=K_{j_1}^{-1}\cdots K_{j_\ell}^{-1}.\end{aligned}\tag{19}
```

 $m(p)$  的调用数为  $9\ell$ ，且对于实初态  $v$ ，
 $K_ {m(p)}v=\overline{K_ pv}$ 。


**证明。**

第一式逐因子使用式 [(13)](#eq-eq:mirror-covariance)，中间的  $S^\dagger S$  消去。
因为每个  $\mathcal P_ j$  实，
 $\overline{K_ j}=\zeta^{-1}[(I-\mathcal P_ j)+\zeta^{-1}\mathcal P_ j]=K_ j^{-1}=K_ j^9$ 。
逐项共轭保持矩阵乘法次序，给第二式。
一般乘积取逆反转次序，给第三式。
最后  $\overline v=v$ ，所以  $\overline{K_ p}v=\overline{K_ pv}$ 。

**证毕。**


这项构造使用已知的程序描述和指定的实初态。
它没有构造一个与未知输入无关的装置，使所有  $\psi$  都被送到  $\overline\psi$ 。
在抽象编织群中， $\sigma_ i\mapsto\sigma_ i^{-1}$  是保持乘法次序的镜像自同构；
 $g\mapsto g^{-1}$  则反转乘法次序。静态图仍须保留有向组合，不能因没有外部时间就交换这些操作。


<a id="stmt-6-3"></a>

#### 命题 6.3：相对程序的读出与共同镜像不变性

给定同一归一实参考  $v$ ，把  $K_ pv$  作为制备射线、 $K_ qv$  作为一个秩一读出方向，
其 Born 配对为

<a id="eq-eq:relative-readout"></a>

```math
P(q\mid p)=|\langle v,K_q^\dagger K_pv\rangle|^2.\tag{20}
```

同时把两个射线作用同一酉算子，或者同时共轭二者，均保持此配对。
特别地， $P(s(q)\mid s(p))=P(q\mid p)$ 、
 $P(m(q)\mid m(p))=P(q\mid p)$ 。


**证明。**

第一式是两个射线重叠的定义。
共同酉作用在内积中抵消；共同共轭把内积取复共轭，模平方不变。
使用  $Sv=v$  与上一规则即得两个具体等式。

**证毕。**


式 [(20)](#eq-eq:relative-readout) 表达用户“测量是两个门序列的相对关系”的一部分精确含义：
配对只依赖相对矩阵  $K_ q^\dagger K_ p$ 。
它既不把所有态认作同一个态，也不证明 Born 配对本身由这一消去式推出。
若只改变制备而保持读出方向，概率可以改变；例如  $\lvert +i\rangle$  与自身的配对为一，
将制备单独共轭为  $\lvert -i\rangle$  后，与原读出的配对为零。


<a id="sec:gap"></a>

## 7. 十三维反手性换框的精确障碍与扩充方式

取边界地址  $K=K_ 0|_ H$ 、 $P=\mathcal P_ 0|_ H$ 。
左邻固定为一，故  $Pe_ \beta=\beta_ 1e_ \beta$ 。
 $\beta_ 1=1$  强迫  $\beta_ 2=0$ ，剩余三位有  $a_ 3=5$  种； $\beta_ 1=0$  时剩余四位有  $a_ 4=8$  种。
所以  $K$  的本征值与重数为

<a id="eq-eq:58"></a>

```math
\zeta\ (8\text{ 重}),\qquad \zeta^2\ (5\text{ 重}).\tag{21}
```

这也是项目命题 85.2 已列出的边界投影。
[\[3\]](#bib-repoborn)


<a id="stmt-7-1"></a>

#### 命题 7.1：固定酉换框不能反转该门的谱手性

不存在  $U\in U(13)$ 、 $|c|=1$  使  $UKU^\dagger=cK^{-1}$ 。


**证明。**

左侧两个不同本征值的重数为  $8,5$ ；右侧分别为  $c\zeta^{-1}$  与  $c\zeta^{-2}$ ，重数也为  $8,5$ 。
不同重数迫使按相同重数匹配，于是同时要求  $c=\zeta^2$  与  $c=\zeta^4$ ，矛盾。

**证毕。**


逆门  $K^9$  仍精确可执行。命题限制的是“把整件门以固定复线性换框变成逆门”这一共轭任务。
还可以把该障碍加强为正距离。


<a id="stmt-7-2"></a>

#### 定理 7.2：反手性酉共轭轨道的精确间隙

对式 [(21)](#eq-eq:58) 的原生边界门，

<a id="eq-eq:chiral-gap"></a>

```math
\boxed{\inf_{U\in U(13),\,|c|=1}
 \|UKU^\dagger-cK^{-1}\|_{\rm op}=2\sin\frac{3\pi}{20}.}\tag{22}
```


**证明。**

记  $D_ P=I+(e^{i\theta}-1)P$ ， $K=e^{i\theta}D_ P$ 。
去掉自由整体相位、左乘酉矩阵，可把问题写成

```math
\inf_{\operatorname{rank} Q=5,\,|d|=1}\|D_PD_Q-dI\|_{\rm op},
 \qquad Q=UPU^\dagger.
```

两个等秩投影的主角分解把  $H$  写成五个二维块与一个三维余块。
在每个二维块中，

```math
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
 Q=\begin{pmatrix}\cos^2\beta&\cos\beta\sin\beta\\  \cos\beta\sin\beta&\sin^2\beta\end{pmatrix},
 \quad0\le\beta\le\frac\pi2;
```

三维余块上两投影都为零。
该分解可由  $PQP$  在  $\operatorname{ran}P$  上对角化取得；
对  $0\lt \cos^2\beta\lt 1$ ，把  $Q$  作用到相应本征向量后正交化给配对的补向量。
对本征值零或一使用相交／正交子空间；
因  $13\ge2\cdot5$ ，共同零空间足以补齐所有端点块。

因此  $D_ PD_ Q$  必含本征值  $1$ 。
在任一二维块，其行列式为  $e^{2i\theta}$ ，迹为
 $2e^{i\theta}[1-(1-\cos\theta)\cos^2\beta]$ ，所以另两本征值为

```math
e^{i(\theta-\omega)},\quad e^{i(\theta+\omega)},\qquad
 \cos\omega=1-(1-\cos\theta)\cos^2\beta,\quad0\le\omega\le\theta.
```

取三点的圆周角  $0,\theta-\omega,\theta+\omega$ 。
相邻圆周间隙为
 $\theta-\omega,\thinspace 2\omega,\thinspace 2\pi-\theta-\omega$ 。
在  $\theta=3\pi/5$  时，每个间隙都不超过  $2\pi-\theta$ ，
因为  $\theta\le2\pi-\theta$ 、 $2\theta\le2\pi-\theta$ 。
故包含这三点的最短闭弧长至少为  $\theta$ 。
任一中心相位到至少一个谱点的圆周距离不小于  $\theta/2$ ，
弦长至少  $2\sin(\theta/4)$ 。酉矩阵是正规矩阵，算子范数就是最大谱距离，得到下界。

取  $Q$  与  $P$  正交是可能的，因为  $5+5\le13$ 。
此时  $D_ PD_ Q$  在两者像空间的和上等于  $e^{i\theta}$ ，在三维余块上等于一。
选  $d=e^{i\theta/2}$  时两个谱距离均为  $2\sin(\theta/4)$ ，达到下界。
换回原  $K$  的相位为  $c=e^{5i\theta/2}=-i$ 。

**证毕。**


这一结论只针对所列谱和任务，不能推广成“所有门都不能酉换框到逆门”。
在二维实秩一模型中，令  

```math
Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)
```

 ，
对任一实秩一投影都有  $YPY=I-P$ ，从而

```math
YK_PY=\zeta^3K_P^{-1}.
```

二维的  $1+1$  重数平衡允许这一换框；十三维的  $5+8$  分裂不允许。


<a id="stmt-7-3"></a>

#### 命题 7.3：保留手性标记的酉实现

在新增空间  $\widetilde H=H_ +\oplus H_ -\simeq H\otimes\mathbb C^2$  上，定义

<a id="eq-eq:double"></a>

```math
\widetilde K_j=K_j\oplus\overline{K_j},\qquad
 J_\chi(\psi_+,\psi_-)=(\psi_-,\psi_+).\tag{23}
```

则  $J_ \chi$  为复线性酉对合，且
 $J_ \chi\widetilde K_ jJ_ \chi=\widetilde K_ j^{-1}$ 。
记  $\rho(\sigma_ {j+1})=K_ j$ 、 $\widetilde\rho=\rho\oplus\overline\rho$ 。
对任意编织字  $b$ ，若  $\kappa$  逐生成元送  $\sigma_ i$  到  $\sigma_ i^{-1}$ ，则
 $J_ \chi\widetilde\rho(b)J_ \chi=\widetilde\rho(\kappa(b))$ 。


**证明。**

块交换显然酉且自逆，交换两块后为
 $\overline{K_ j}\oplus K_ j=K_ j^{-1}\oplus K_ j$ 。
逐因子相乘保持顺序，所以给镜像自同构的表示，而不一般给整个字的逆。

**证毕。**


这里增加的是二十六维载体和一个手性标记，未声称当前十三维无辅助位模型已经供应它。
 $J_ \chi$  保持各分量的未知复系数，只改变它所在的扇区；它仍不是对固定扇区内未知态作普遍共轭。


<a id="sec:gram"></a>

## 8. 非正交读出的酉镜像：完整 Gram 与闭环判据

用户提出稳定读出间的隐藏连线关系，这里可以精确化。
若五个标签被编码为  $H$  中的五条射线，单看点的位置和两两概率还不一定足够。
所需数据是一个正半定的复 Gram 矩阵。


<a id="stmt-8-1"></a>

#### 定义 8.1：读出关系矩阵与闭环

对于归一化向量族  $v_ 1,\ldots,v_ N$ ，定义  $G_ {ij}=\langle v_ i,v_ j\rangle$ 。
非零重叠图在  $G_ {ij}\ne0$  时连接  $i,j$ 。
对其有向闭环  $C=(i_ 0,\ldots,i_ k=i_ 0)$ ，定义

<a id="eq-eq:bargmann"></a>

```math
B_C(v)=\prod_{a=0}^{k-1}G_{i_a i_{a+1}}.\tag{24}
```

它不随各向量代表的独立相位而变，是相位规范不变量。


<a id="stmt-8-2"></a>

#### 引理 8.2：完整 Gram 矩阵判据

同一有限维  $H$  中两组向量  $v_ i,w_ i$  可由同一酉算子满足  $Uv_ i=w_ i$ ，
当且仅当  $G^v=G^w$ 。


**证明。**

必要性由内积保持。充分性定义
 $U(\sum_ i a_ iv_ i)=\sum_ i a_ iw_ i$ 。
若左侧表示零，其范数平方为  $a^\dagger G^va=0$ ；Gram 相同使右侧也为零，故定义良好。
相同恒等式保持任意两向量内积，且映到整个目标张成空间。
两个张成空间等维，其正交补也等维，选补空间正交基即可延拓为全空间酉算子。

**证毕。**


<a id="stmt-8-3"></a>

#### 定理 8.3：射线镜像的全闭环充要条件

对于两组归一化向量  $v_ i,w_ i$ ，存在  $U\in U(H)$  与  $|g_ i|=1$ ，
使  $Uv_ i=g_ iw_ i$  对全部  $i$  成立，当且仅当

<a id="eq-eq:gram-cycle"></a>

```math
\begin{gathered}
|G^v_{ij}|=|G^w_{ij}|\quad\text{对全部 }i,j,
 \qquad\\ \prod_{(i,j)\in C}\frac{G^v_{ij}}{G^w_{ij}}=1
 \quad\text{对每个非零重叠闭环 }C.\end{gathered}\tag{25}
```

第一条件也包含零模式一致。


**证明。**

必要性：内积保持给
 $G^v_ {ij}=\overline{g_ i}g_ jG^w_ {ij}$ ；
取模得到第一式，沿闭环相乘后所有顶点相位消去。

充分性：在每个非零重叠连通分量选根，置根的  $g=1$ 。
沿任意根到  $i$  的路径，把边比值  $r_ {jk}=G^v_ {jk}/G^w_ {jk}$  相乘定义  $g_ i$ 。
由于反向边比值是逆元，任两路径之差给一个闭游走；闭环条件保证值不依赖路径。
于是  $r_ {ij}=\overline{g_ i}g_ j$ ，得到  $v_ i$  与  $g_ iw_ i$  的全部 Gram 元相同，
包括零项及对角项。应用上一引理。

**证毕。**


检验一棵生成森林的基本闭环就足够；只检查三角形则未必足够。
若重叠图有较长的无三角闭环，那里仍可能藏有相位障碍。
这与既有 v23 的平坦连接思想相容，但这里直接给出了指定有限读出族的酉可实现充要条件。


<a id="stmt-8-4"></a>

#### 推论 8.4：反酉支

存在反酉  $A$  与逐态相位使  $Av_ i=g_ iw_ i$ ，
当且仅当两组重叠模相同、零模式相同，并且每个目标闭环值为对应源闭环值的复共轭。


**证明。**

反酉使内积共轭；把源向量族换为  $\overline{v_ i}$  后，应用上一定理。

**证毕。**


<a id="stmt-8-5"></a>

#### 命题 8.5：三态已能锁定两两概率遗漏的手性

取

```math
v_1=\lvert 0\rangle,\qquad v_2=\frac{\lvert 0\rangle+\lvert 1\rangle}{\sqrt2},\qquad
 v_3=\frac{\lvert 0\rangle+i\lvert 1\rangle}{\sqrt2},\qquad w_i=\overline{v_i}.
```

两组的每对不同射线转移概率均为  $1/2$ ，
但不存在同一个酉算子在允许逐态相位后实现全部  $v_ i\mapsto w_ i$ 。


**证明。**

直接相乘得

```math
B_{123}(v)=\langle v_1,v_2\rangle
 \langle v_2,v_3\rangle\langle v_3,v_1\rangle=\frac{1+i}{4},
 \qquad B_{123}(w)=\frac{1-i}{4}.
```

它们不同，违背式 [(25)](#eq-eq:gram-cycle)；各边重叠模平方仍为  $1/2$ 。

**证毕。**


对纯量子比特投影  $\rho_ a=(I+\mathbf a\cdot\sigma)/2$ ，同一现象可写为

<a id="eq-eq:triple-bloch"></a>

```math
\operatorname{Tr}(\rho_a\rho_b\rho_c)
 =\frac{1+\mathbf a\cdot\mathbf b+\mathbf b\cdot\mathbf c
 +\mathbf c\cdot\mathbf a+i\,\mathbf a\cdot(\mathbf b\times\mathbf c)}4.\tag{26}
```

展开 Pauli 乘法即证明此式。两两概率只见点积，虚部见有向三重积。
但若只是把图中同一闭环的遍历方向反过来， $B_ C$  也会共轭；
这属于标签顺序改变，不能因此断言物理态遭到了反酉操作。


<a id="stmt-8-6"></a>

#### 命题 8.6：正半定关系数据的构造与镜像提升

设有限标签集  $\mathcal A$  上给出  $G\succeq0$ 、 $G_ {aa}=1$ 。
商空间  $\mathbb C^{\mathcal A}/\ker G$  配以内积
 $\langle[a],[b]\rangle=a^\dagger Gb$ ，得到一个有限维希尔伯特空间和实现  $G$  的向量族。
若标签镜像  $m$  是满足  $m^2=\operatorname{id}$  的置换，且
 $G_ {m(a)m(b)}=G_ {ab}$ ，则它在此商空间诱导酉对合。


**证明。**

正半定矩阵的零范数向量恰为  $\ker G$ ，取商后内积正定。
坐标基的商类给所需向量；标签置换保持二次型，故保持核并在商空间保持内积。
若  $m^2=1$ ，其提升也平方为一。

**证毕。**


这个命题回答“图本身怎样成为希尔伯特空间”的一个可操作版本：
需要提供正半定复关系核，而不只是无权的点与边。
对 AURIC 五标签，可以明确写出  $5\times5$  的  $G$ 、其秩、镜像置换及闭环不变量再检验。
若三个读出被规定为正交，三者之间的重叠全为零，反而不提供相对复相位；
相位须由与其余读出、混合态方向或实际干涉器的关系来取得。
因此“三个正交方向”本身不唯一固定全部隐藏量子关系。


<a id="sec:transpose"></a>

## 9. 真正的 Bloch 镜像为何需要噪声：完全正性与最优界

本节固定有限维数  $d\ge2$ ，在标准量子信道框架内工作。
其结论为已知最优转置定理的自足重证，
不把完全正性或 Born 概率假定成由 Hat 外形已经推出。
[\[16\]](#bib-transpose) [\[17\]](#bib-watrous)


<a id="stmt-9-1"></a>

#### 定义 9.1：信道与未知态共轭任务

确定性量子信道  $\Phi$  是算子空间上的复线性、保迹、完全正映射。
完全正要求  $\operatorname{id}_ R\otimes\Phi$  对任意参考系统仍保持正算子。
向量共轭  $C\psi=\overline\psi$  在纯态投影上的目标作用是
 $\rho\mapsto\rho^{\mathsf T}$ 。向量上的  $C$  反线性，
算子上的转置映射  $\mathcal T(X)=X^{\mathsf T}$  则复线性；问题是后者不完全正。


<a id="stmt-9-2"></a>

#### 定理 9.2：普遍未知态共轭的 Bell 障碍

当  $d\ge2$  时，转置正且保迹，但不完全正。
因此不存在确定性量子信道在每个未知纯态上实现其共轭纯态。


**证明。**

令  $\lvert \Omega\rangle=d^{-1/2}\sum_ i\lvert ii\rangle$ ， $F$  为两份  $\mathbb C^d$  的交换算子。
直接展开有

```math
(\operatorname{id}\otimes\mathcal T)(\lvert \Omega\rangle\langle \Omega\rvert)
 =\frac1d\sum_{ij}\lvert i\rangle\langle j\rvert\otimes\lvert j\rangle\langle i\rvert=\frac Fd.
```

对  $i\ne j$  的反对称向量  $(\lvert ij\rangle-\lvert ji\rangle)/\sqrt2$ ，本征值为  $-1/d$ ，
故结果不是正算子。
若某信道在全部纯态投影上等于转置，谱分解使它在全部厄米算子上等于转置；
复线性再使它在全部算子上相等，与上述反例矛盾。

**证毕。**


该论证不排除反酉作为数学上的射线对称，也不排除第 6 节对已知程序做镜像编译。
它排除的是：对任意未知输入，包括与任意外部参考纠缠的输入，执行同一个局部共轭信道。


<a id="stmt-9-3"></a>

#### 引理 9.3：均匀纯态的二阶矩

令  $\rho_ \psi=\lvert \psi\rangle\langle \psi\rvert$ ， $\psi$  均匀分布于  $\mathbb C^d$  的单位球面，则

<a id="eq-eq:haar"></a>

```math
\mathbb E(\rho_\psi\otimes\rho_\psi)=\frac{I+F}{d(d+1)}.\tag{27}
```


**证明。**

各坐标独立相位旋转不改变分布，因此四阶矩非零时，正负相位指标必须配对。
坐标置换不变性留下两个数
 $a=\mathbb E|\psi_ 1|^4$ 、 $b=\mathbb E|\psi_ 1|^2|\psi_ 2|^2$ 。
用  $(\psi_ 1+\psi_ 2)/\sqrt2$  替换第一坐标并对相位平均，得到
 $a=(2a+4b)/4$ ，所以  $a=2b$ 。
再用  $(\sum_ j|\psi_ j|^2)^2=1$ ，
有  $da+d(d-1)b=1$ ，故  $b=1/[d(d+1)]$ 。
逐矩阵元代入正好给式 [(27)](#eq-eq:haar)。

**证毕。**


<a id="stmt-9-4"></a>

#### 定理 9.4：任意维数的最优确定性近似共轭；已知定理的重证

定义

<a id="eq-eq:optimaltranspose"></a>

```math
\Phi_*(X)=\frac{X^{\mathsf T}+\operatorname{Tr}(X)I}{d+1}.\tag{28}
```

它是 CPTP 信道，对每个纯态  $\rho$  均有
 $\operatorname{Tr}[\rho^{\mathsf T}\Phi_ *(\rho)]=2/(d+1)$ 。
对任意 CPTP 信道  $\Phi$ ，

<a id="eq-eq:optimalbound"></a>

```math
\mathbb E_\rho\,\operatorname{Tr}[\rho^{\mathsf T}\Phi(\rho)]
 \le\frac2{d+1},
 \qquad
 \sup_\Phi\inf_{\rho\ {\rm pure}}\operatorname{Tr}[\rho^{\mathsf T}\Phi(\rho)]
 =\frac2{d+1}.\tag{29}
```

这里没有先限制  $\Phi$  为协变或各向同性信道。


**证明。**

使用未归一 Choi 矩阵
 $J_ \Phi=\sum_ {ij}\lvert i\rangle\langle j\rvert\otimes\Phi(\lvert i\rangle\langle j\rvert)$ 。
标准 Choi 判据说  $\Phi$  完全正当且仅当  $J_ \Phi\succeq0$ ，
保迹当且仅当对输出偏迹为  $I$ 。
对式 [(28)](#eq-eq:optimaltranspose)，
 $J_ *=(F+I)/(d+1)$  是对称子空间投影乘  $2/(d+1)$ ，所以正；
又  $\operatorname{Tr}_ {\rm out}F=I$ 、 $\operatorname{Tr}_ {\rm out}I=dI$ ，故保迹。
对纯态代入，目标保真度为  $(1+1)/(d+1)$ 。

对于任一信道， $J=J_ \Phi\succeq0$ 、 $\operatorname{Tr} J=d$ ，并且
 $\operatorname{Tr}[\sigma\Phi(\rho)]=\operatorname{Tr}[J(\rho^{\mathsf T}\otimes\sigma)]$ 。
令  $\sigma=\rho^{\mathsf T}$ ，利用共轭不改变均匀测度及式 [(27)](#eq-eq:haar)，

```math
\mathbb E_\rho\,\operatorname{Tr}[\rho^{\mathsf T}\Phi(\rho)]
 =\frac{\operatorname{Tr}[J(I+F)]}{d(d+1)}
 \le\frac{2\operatorname{Tr} J}{d(d+1)}=\frac2{d+1}.
```

不等式来自  $I+F\preceq2I$  和  $J\succeq0$ 。
任一信道的最坏值不大于其平均值； $\Phi_ *$  对每个纯态都达到该常数，故也达到最坏情形最优值。

**证毕。**


<a id="stmt-9-5"></a>

#### 推论 9.5：量子比特的镜像可见度上限

各向同性噪声镜像

```math
\Phi_\eta(X)=\eta X^{\mathsf T}+(1-\eta)\operatorname{Tr}(X)I/d
```

完全正的范围恰为

```math
-\frac1{d-1}\le\eta\le\frac1{d+1}.
```

特别在  $d=2$ 、 $\eta\ge0$  时，

<a id="eq-eq:visibility"></a>

```math
(r_x,r_y,r_z)\longmapsto\eta(r_x,-r_y,r_z)
 \quad\text{可实现当且仅当}\quad0\le\eta\le\frac13.\tag{30}
```

最优纯态目标保真度为  $2/3$ 。


**证明。**

 $J_ \eta=\eta F+(1-\eta)I/d$ 。
其对称与反对称子空间的本征值分别为
 $[1+(d-1)\eta]/d$  和  $[1-(d+1)\eta]/d$ 。
两者非负恰给所述区间；偏迹始终为  $I$ 。
量子比特的目标保真度为  $(1+\eta)/2$ ，在  $\eta=1/3$  达到  $2/3$ 。
任何其他  $\det O=-1$  的 Bloch 正交映射，都可在该镜像后复合一个酉旋转，所以同样适用。

**证毕。**


这里收缩的是约化态的 Bloch 半径，完整系统加环境的纯态仍可酉演化并保持范数。
真正的  $2P-I$  酉反射无须加入这些噪声。
只有把目标任务改成普遍未知态共轭，才遇到本节的界。
因此，“镜像都应刚性无缩放”不能同时作为这两种任务的定义。


<a id="sec:latest"></a>

## 10. 静态关系中的观察者：共同换框、真实菜单与最新时钟


<a id="subsec-10-1"></a>

### 10.1 静态相容性与完整记录


<a id="stmt-10-1"></a>

#### 定义 10.1：带仪器的观测模型

一个有限观测模型包含状态  $\rho$ 、每个设置及结果对应的完全正仪器分支  $\mathcal I_ {a|s}$ ，
以及取得记录后允许的下一设置规则。
对每个设置， $\sum_ a\mathcal I_ {a|s}$  保迹。
完整记录  $h=(a_ 1,\ldots,a_ \ell)$  的质量为
 $\operatorname{Tr}[\mathcal I_ {a_ \ell|s_ \ell}\circ\cdots\circ\mathcal I_ {a_ 1|s_ 1}(\rho)]$ ，
其中后续  $s_ i$  可以依赖已经取得的记录。
模型中的有向复合是静态逻辑数据，不要求另加连续外部时钟。


<a id="stmt-10-2"></a>

#### 定理 10.2：共同换框保持全部有限记录律

给定酉算子  $W$ ，同步变换

```math
\rho'=W\rho W^\dagger,\qquad
 \mathcal I'_{a|s}=\operatorname{Ad}_W\circ\mathcal I_{a|s}\circ\operatorname{Ad}_{W^\dagger},
```

并保持同一记录到设置的规则，则所有完整有限记录质量不变。
在固定基中同步共轭  $\rho$  及所有分支 Kraus 矩阵，也得到另一个合法模型并保持全部记录质量。


**证明。**

酉情形的相邻  $\operatorname{Ad}_ {W^\dagger}\operatorname{Ad}_ W$  逐次消去，末端迹不变。
若分支 Kraus 算子为  $A_ {a,r|s}$ ，共轭后为  $\overline{A_ {a,r|s}}$ ，
完整性等式逐项共轭仍成立，故新分支仍完全正且总和保迹。
每条细化记录的乘积矩阵同步共轭，终端质量为原非负实数的共轭，因而相等。
对隐藏 Kraus 指标求和保持等式；相同记录使自适应规则选择相同设置，归纳完成。

**证毕。**


这项模型对应不提供一个主动反酉门。
内生观察者若连同其参考、仪器和标签一起变换，全部记录可不变；
把世界的一部分镜像而保留另一部分相位参考，则可能产生可读出的相对差异。
项目原重构第 25 节及续卷第 53--56、65 节已研究这个区别，本稿不把它当作本轮首次提出。
[\[5\]](#bib-repocore) [\[6\]](#bib-repocont)

相干重构续卷 II 的最新第 91--95 节也仍要求实际记录质量、分支响应转移和忽略记录后的设置隔离三个接口。
写出理想等距矩阵并不供应这些接口。
该源码还证明真实执行历史若被正交档案保留，会消去所需交叉项；
空制备例子的读出质量由目标  $(a,b)$  变为  $(3/5,2/5)$ ，其中
 $a=(5+\sqrt5)/10$ 、 $b=(5-\sqrt5)/10$ 。
[\[3\]](#bib-repoborn)
对镜像问题同样如此：替换程序、反序配置、改变参考和读取档案是四种具体模型操作，须逐一给出。


<a id="subsec-10-2"></a>

### 10.2 本轮新时钟结果怎样支持静态分析


最新周期时钟文稿给出的对象是一个指定的二进制递推来源  $s$ ，
其对齐周期核心  $y$  的最小周期为  $p$ ，并带有限暂态。
在真实物理节点  $v$ ， $A_ v,B_ v$  是前两批出生索引，
 $e_ v$  是该节点的 beta 归一化起点， $c_ v=s_ {A_ v-1}$ 。
新定理 17.2 给出以下整数关系，而不是仅给抽象图可达性：
[\[8\]](#bib-repoclock)


|  $c_ v$  | 子节点  $a$  的  $(A,B)$  | 子节点  $b$  的  $(A,B)$  |  $(\delta_ a,\delta_ b)$  |
|---|---|---|---|
|  $1$  |  $(B,A+B)$  |  $(A+B+1,A+2B+2)$  |  $(1,2)$  |
|  $0$  |  $(A+B,A+2B)$  |  $(B,A+B+1)$  |  $(2,1)$  |


根为  $(e,A,B)=(1,1,2)$ ，而  $e_ {vx}=e_ v+\delta_ x(c_ v)$ 。
这些是项目给定来源模型中的公式，并未断言这些整数映射就是量子门。

令  $E_ s$  为真实安全核心种子的模  $p$  余数集，
 $N_ y$  为两条命名子边的计数矩阵（列为出发状态）。
项目新定理 19.2 证明实际核心安全锥的余数像恰为

<a id="eq-eq:clockimage"></a>

```math
R_s=\operatorname{supp}\left[
 \left(\sum_{j=0}^{p^2-|E_s|}N_y^j\right)\mathbf 1_{E_s}\right].\tag{31}
```

每条从真实种子  $c$  出发的图路径  $w=x_ 1\cdots x_ h$  都提升到真实地址  $cw$ ，且

<a id="eq-eq:clocktime"></a>

```math
e_{cw}=e_c+\sum_{i=1}^h
 \delta_{x_i}\!\left(c_y(A_{cx_1\cdots x_{i-1}})\right),
 \qquad n=e_{cw}+T.\tag{32}
```

 $T$  是局部年龄， $n$  才是该局部观察所在的真实切面。
这两式连同实际种子刻画是所引源码的新定理；本稿不重证其全部来源递推。


<a id="stmt-10-3"></a>

#### 命题 10.3：无权商图何时丢失切面

对于任何带实际种子起点  $e_ c$  和边延迟  $\delta$  的有向路径模型，
若从同一个实际种子  $c$  出发的两条路径到达同一商状态而累计延迟不同，
则保留该商状态及共同局部年龄  $T$ 
不足以恢复真实切面  $n=e_ c+\sum\delta+T$ 。


**证明。**

两条路径的保留状态和  $T$  相同，但右侧给出的  $n$  不同。
故不存在只依赖这些保留数据的单值恢复函数。

**证毕。**


项目新例子中，同一个对齐核心  $y=(10)^\infty$ ，
纯周期来源只达到两个余数；添加允许的第一位暂态后，来源  $001010\ldots$  可达到全部四个模二状态。
故实际时钟像不由周期核心单独确定。
与用户的静态图观点相容的形式是：把种子、来源依赖、边延迟和相位一起写在静态关系中；
删除这些信息后的无权图不能代表全部观测结构。
边延迟是该经典递推模型中的整数，并不因此等于量子相位或物理时长。
[\[8\]](#bib-repoclock)


<a id="subsec-10-3"></a>

### 10.3 同容限覆盖障碍与“每个观察者都能猜到”


最新自标定 IV 第 21 节在四维严格正、秩至多二的来源模型中证明：
对每个固定有限  $\varepsilon\gt 0$ ，存在来源族  $Q_ {\varepsilon,s}$ ，
每个来源各有一个全域可靠的确定性策略，能在所有允许误差历史中用七报告认出其秩二；
但任一这样的策略至多对该族的一个参数全误差成功。
因此有限子族  $T$  的同容限覆盖数为  $|T|$ ，整个成功域没有有限覆盖。
[\[7\]](#bib-repoself)

其前提包括一条不可复制、不可复位的轨迹，固定操作菜单  $\lbrace N,L_ 0\rbrace$ ，强制报告，
以及闭误差区间  $[-\varepsilon,\varepsilon]$ 。
这里的量词是

```math
\forall s\ \exists\Pi_s\ \forall\text{允许历史},
 \qquad\text{不能替换为}\qquad
 \exists\Pi\ \forall s\ \forall\text{允许历史}.
```

来源各自存在成功预测过程，不供应一个知道应选哪种策略的内生选择器。
同一证明中的正比例变换同时缩放来源、报告与误差容限；
它不提供保持同一绝对误差预算的免费归一化。
原菜单也没有主动镜像：坐标反序会把  $N$  送成  $N^{\mathsf T}$ ，
把  $L_ 0=e_ 0\mathbf 1^{\mathsf T}$  送成  $e_ 3\mathbf 1^{\mathsf T}$ ，
所以只能说完整变换后的模型对应，不能说原菜单已经闭合于镜像。


<a id="section-11"></a>

## 11. 面向 AURIC 五模式的建设性研究形式


<a id="stmt-11-1"></a>

#### 定义 11.1：带相位关系的量子铺砌模型

一个可审查的有限模型至少包含：
合法配置或标签集合  $\mathcal C$ ；
读出向量的正半定复关系核  $G$ ；
允许的局部门及其可调用地址；
接口重组、镜像和闭环相容规则；
初始制备、实际仪器、完整记录及近似误差范数。
用有向网络把这些对象连接，可以不选外部连续时间，
但输入输出类型和非交换的复合次序仍是网络的一部分。


对五标签  $\lbrace \mathrm{null},1,2,3,13\rbrace$ ，可从如下具体问题推进：
为全部标签写出同一个  $G$ ，明确它们是正交配置、非正交读出还是一个态的不同坐标；
给出几何镜像在这些标签上的作用；
用式 [(25)](#eq-eq:gram-cycle) 检验它是否有酉提升；
再检查提升能否由指定原生菜单精确或近似实现。
第 [5](#sec:28) 节已经完成原生链空间镜像这一实例，
第 [7](#sec:gap) 节则表明把空间镜像换成谱手性反转后，答案会改变。


<a id="stmt-11-2"></a>

#### 命题 11.2：带显式控制接口的镜像可以参与纠缠生成

设  $U_ m$  是配置酉对合， $Q$  是内部系统的投影， $K$  是内部酉门。
如果操作菜单额外供应

```math
S_m=(I-Q)\otimes I+Q\otimes U_m,
 \qquad W=S_m(K\otimes I),
```

则  $W$  酉。若  $\chi$  是单位向量、 $T\ne mT$  且
 $0\lt \Vert QK\chi\Vert ^2\lt 1$ ，输入  $\lvert \chi\rangle\otimes\lvert T\rangle$  的输出具有 Schmidt 秩二。


**证明。**

 $S_ m$  在两个正交控制子空间分别为  $I$  与  $U_ m$ ，故酉且自逆。
输出为

```math
((I-Q)K\lvert \chi\rangle)\otimes\lvert T\rangle
 +(QK\lvert \chi\rangle)\otimes\lvert mT\rangle.
```

两内部向量正交、两配置正交，且两系数非零，所以这是含两项的 Schmidt 分解。

**证毕。**


这给出把刚性配置镜像和 AURIC 相干混合连接起来的一个明确方案。
其控制接口是额外假设；不能因非受控镜像已经存在，就默认受控版本也已原生可用。
它单独证明纠缠生成，不单独证明多比特普适性。


| 命题或问题 | 本轮能给出的严格状态 |
|---|---|
| 原生  $K$  是否包含反射 |  $K^5=2P-I$ ，有限精确，继承已核对结果 |
| 原生左右镜像是否可执行 |  $\Delta_ K=e^{i\chi}S$ ，28 次正调用；本轮推论 |
| 已知程序是否可镜像 | 保持调用次序、每门换成九次，精确给  $\overline{K_ p}$  |
| 十三维固定换框是否可反手性 | 不可；精确距离为  $2\sin(3\pi/20)$  |
| 五非正交读出的镜像如何判定 | 重叠模、零模式与全部非零闭环条件充要 |
| 未知态普遍共轭是否为酉门 | 不是 CPTP；最优确定性近似为已知转置信道 |
| Hat 外形能否唯一推出复结构与 Born 权重 | 当前构造未做到；必须补齐关系核、组合与实际读出接口 |
| 黄金层级缩放是否破坏酉性 | 需区分有限矩阵扩张、空间函数酉伸缩、重标尺及记录增长 |


本轮可成立的核心表述是：
*帽子刚性镜像与量子门之间存在严格的表示桥；AURIC 原生门已经给出有限可编译的空间镜像，
而完整量子相容性进一步由复内积、闭环相位、谱重数和实际观测接口约束。*
这使“边上隐藏关系”的直觉成为可定义、可证明、也可被反例否定的研究对象。

## 文献与固定项目来源

<a id="bib-repohead"></a>

- **[1]** The Omega Institute, *trureturing*。
[固定提交 66259f03d607](https://github.com/the-omega-institute/trureturing/commit/66259f03d60716f143cd59c7644dadcb67cc1b73)，
2026-10-30 10:26:54 UTC。
本轮通过 Git API 实际下载源码并核对 blob；数学推导不以提交合并作为认证。

<a id="bib-repov15"></a>

- **[2]** 项目，[AURIC 黄金门、NAND 普适性与算术边界 v15](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)，同一固定提交，第 3--6 节。
本轮未变；本文第 4 节的幂、闭包和旧相位间隙来自此文。

<a id="bib-repoborn"></a>

- **[3]** 项目，[量子基本原则与相干重构续卷 II](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，同一固定提交，第 77、85、91--95 节。
blob `df7a682c8e1bc279c50c1557380b595eddc5d0e6`，相对 v26 未变。

<a id="bib-repov23"></a>

- **[4]** 项目，[非周期单砖、酉投影、三角中心与递归变分 v23](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_APERIODIC_MONOTILES_UNITARY_PROJECTIONS_TRIANGLE_CENTRES_AND_RECURSIVE_VARIATION_V23.md)，同一固定提交。
该文件注明是先前稿件的入库转换，不是独立认证。

<a id="bib-repocore"></a>

- **[5]** 项目，[量子基本原则与相干重构](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)，同一固定提交，第 25 节。

<a id="bib-repocont"></a>

- **[6]** 项目，[量子基本原则与相干重构续卷](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，同一固定提交，第 38、53--56、65 节。

<a id="bib-repoself"></a>

- **[7]** 项目，[自标定关系数学 IV](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)，同一固定提交，新第 21 节，尤指定理 21.6--21.7。
本文仅在其原严格正、固定容限和操作菜单范围内引用。

<a id="bib-repoclock"></a>

- **[8]** 项目，[递归关系观察的周期时钟刚性](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md)，同一固定提交，新第 17--21 节，
尤指定理 17.2、19.2、21.1 与命题 20.1。

<a id="bib-repospider"></a>

- **[9]** 项目，[不等长蜘蛛图幂的零强制](https://github.com/the-omega-institute/trureturing/blob/66259f03d60716f143cd59c7644dadcb67cc1b73/docs/develop/theory/UNEQUAL_SPIDER_POWER_ZERO_FORCING.md)，同一固定提交。列明真实增量，不作量子证据。

<a id="bib-hat"></a>

- **[10]** D. Smith, J. S. Myers, C. S. Kaplan, C. Goodman-Strauss,
*An aperiodic monotile*。
[arXiv:2303.10798v3](https://arxiv.org/html/2303.10798v3)，
第 1.2--1.3、2、5 节。使用其全等定义、双手性与层级结构。

<a id="bib-cap"></a>

- **[11]** M. Baake, F. Gähler, L. Sadun,
*Dynamics and topology of the Hat family of tilings*。
[arXiv:2305.05639v4](https://arxiv.org/html/2305.05639v4)，2025。
使用其手性类区别及形状扩张／CAP 表示。

<a id="bib-householder"></a>

- **[12]** P. A. Ivanov, E. S. Kyoseva, N. V. Vitanov,
*Engineering of arbitrary U(N) transformations by quantum Householder reflections*，
Phys. Rev. A 74, 022323 (2006)。
[arXiv:0708.2811](https://arxiv.org/abs/0708.2811)。

<a id="bib-wigner"></a>

- **[13]** D. D. Spiegel, *A Simple Constructive Proof of Wigner's Theorem*。
[arXiv:1810.10111v2](https://arxiv.org/html/1810.10111v2)，2022 修订。

<a id="bib-garside"></a>

- **[14]** P. Dehornoy, F. Digne, E. Godelle, D. Krammer, J. Michel,
*Foundations of Garside Theory*，EMS Tracts in Mathematics 22，2015。
[作者提供的全文](https://webusers.imj-prg.fr/~jean.michel/papiers/Garside.pdf)，
第 I 章，Reference Structure 2、式 (1.6)。

<a id="bib-flw"></a>

- **[15]** M. H. Freedman, M. J. Larsen, Z. Wang,
*The two-eigenvalue problem and density of Jones representation of braid groups*。
[arXiv:math/0103200v1](https://arxiv.org/html/math/0103200v1)，
Theorem 0.1 与第 2 节。项目第 77.2 节单独核对其表示与原生矩阵的对应。

<a id="bib-transpose"></a>

- **[16]** F. Buscemi, G. M. D'Ariano, P. Perinotti, M. F. Sacchi,
*Optimal realization of the transposition maps*，
Phys. Lett. A 314, 374--379 (2003)。
[arXiv:quant-ph/0304175](https://arxiv.org/html/quant-ph/0304175v1)，
式 (15)--(16)。最优信道与保真度为既有结果。

<a id="bib-watrous"></a>

- **[17]** J. Watrous, *The Theory of Quantum Information*，
Cambridge University Press, 2018。
[作者全文](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，
第 2 章：信道、Choi 判据、等距表示与环境。

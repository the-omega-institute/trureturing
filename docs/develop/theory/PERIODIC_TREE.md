# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);素性位:141/141 本原(城册按类去重后天然本原);$\Psi{=}0$ 节点 12;城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## 8. 黄金连分数支：复位格点、镜面收缩与层际交换缺陷

### 8.1 黄金支、Fibonacci 矩阵与返回映射

**定义。** 令

$$
\alpha=\frac{\sqrt5-1}{2},\qquad \varphi=1+\alpha,
\qquad \psi=-\alpha,
$$

并令 $(F_n)_{n\ge0}$ 为满足 $F_0=0$、$F_1=1$、
$F_{n+2}=F_{n+1}+F_n$ 的 Fibonacci 数列。对 $L\in\mathbb N$，定义

$$
A_L=F_{L+3},\quad B_L=F_{L+2},\quad C_L=F_{L+1},\quad
M_L=\begin{pmatrix}A_L&B_L\\B_L&C_L\end{pmatrix},
$$

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
d_L=\psi^{L+2},\qquad \delta_L=|d_L|.
$$

**定理。** 上述数满足

$$
\alpha^2+\alpha=1,\qquad 0<\alpha<1,\qquad
M_L=Q^{L+2},\qquad \delta_L=\alpha^{L+2},
$$

以及 Cassini 行列式恒等式

$$
\boxed{\det M_L=A_LC_L-B_L^2=(-1)^L.}
$$

因此 $M_L\in GL_2(\mathbb Z)$；$L$ 为偶数时 $M_L\in SL_2(\mathbb Z)$，
$L$ 为奇数时 $M_L$ 反转定向。

**证明。** $\alpha$ 的等式由定义平方后化简得到，且正根的取值给出
$0<\alpha<1$。矩阵幂公式由 Fibonacci 递推归纳得到。对该公式取行列式，
并用 $\det Q=-1$，即得 $\det M_L=(-1)^{L+2}=(-1)^L$。
最后 $|\psi|=\alpha$ 给出 $\delta_L=\alpha^{L+2}$。

**定义。** 对 $m\in\mathbb Z$，定义黄金返回映射

$$
T_L(m)=A_Lm+B_L\lfloor m\alpha\rfloor.
$$

**定理。** 对每个 $L\in\mathbb N$ 与 $m\in\mathbb Z$，

$$
\boxed{T_L(m)=B_L\lfloor m\varphi\rfloor+C_Lm.}
$$

**证明。** 因为 $\varphi=1+\alpha$ 且 $m$ 为整数，
$\lfloor m\varphi\rfloor=m+\lfloor m\alpha\rfloor$。
再用 $A_L=B_L+C_L$ 展开右端即可。

### 8.2 全整数格点与定向相位窗口

**定理。** 若 $m,k\in\mathbb Z$ 且

$$
\binom e h=M_L\binom m k,
$$

则

$$
\boxed{e\alpha-h=d_L(m\alpha-k).}\tag{GC1}
$$

并且整数逆映射为

$$
\boxed{
m=(-1)^L(C_Le-B_Lh),\qquad
k=(-1)^L(A_Lh-B_Le).
}\tag{GC2}
$$

**证明。** Fibonacci 与黄金共轭恒等式给出

$$
B_L\alpha-C_L=-d_L,\qquad
A_L\alpha-B_L=\alpha d_L.
$$

将 $e=A_Lm+B_Lk$、$h=B_Lm+C_Lk$ 代入并合并系数，得到 GC1。
对 $M_L$ 使用上一节的伴随矩阵公式和
$A_LC_L-B_L^2=(-1)^L$，得到 GC2。

**定义。** 对 $e\in\mathbb Z$，定义定向相位窗口事件

$$
\operatorname{Hits}_L(e)
\iff \exists h\in\mathbb Z:\quad
0<\frac{e\alpha-h}{d_L}<1.
$$

**定理。** 对全部 $L\in\mathbb N$ 与 $e\in\mathbb Z$，相位窗口恰好等价于
非零 Beatty 返回：

$$
\boxed{
\operatorname{Hits}_L(e)
\iff \exists m\in\mathbb Z\setminus\{0\}:\ e=T_L(m).
}\tag{GC3}
$$

**证明。** 若 $e=T_L(m)$ 且 $m\ne0$，取
$k=\lfloor m\alpha\rfloor$ 及
$h=B_Lm+C_Lk$。数 $m\alpha$ 不是整数，故
$0<m\alpha-k<1$；GC1 随即给出窗口不等式。
反之，由窗口中的 $e,h$ 按 GC2 恢复 $m,k\in\mathbb Z$。
GC1 把窗口不等式化为 $0<m\alpha-k<1$，所以
$k=\lfloor m\alpha\rfloor$。若 $m=0$，则该不等式要求整数 $k$
严格位于 $(-1,0)$，矛盾；故 $m\ne0$，并且 $e=T_L(m)$。

### 8.3 任意分辨率的收缩与非周期性

**定理。** 对每个 $L\in\mathbb N$，

$$
\boxed{d_{L+1}=-\alpha d_L,\qquad d_{L+2}=\alpha^2d_L.}\tag{GC4}
$$

若 $r\in\mathbb N$ 且 $r>0$，定义
$D_{L,r}=d_L-d_{L+r}$，则

$$
\boxed{D_{L,r}\ne0,\qquad D_{L+1,r}=-\alpha D_{L,r}.}\tag{GC5}
$$

**证明。** 由 $d_L=(-\alpha)^{L+2}$ 直接得到 GC4 及第二个等式。
又有
$|d_{L+r}|=|d_L|\alpha^r<|d_L|$，所以 $d_L\ne d_{L+r}$，
即 $D_{L,r}\ne0$。

**定理。** 对每个 $p\in\mathbb Z$，

$$
\boxed{p\ne0\Longrightarrow p\alpha\notin\mathbb Z.}\tag{GC6}
$$

因此旋转 $x\mapsto x+\alpha\pmod1$ 不存在非零整数回归周期。

**证明。** 若 $p\ne0$ 且 $p\alpha=q\in\mathbb Z$，则
$\alpha=q/p\in\mathbb Q$，这与 $\sqrt5$ 的无理性矛盾。

### 8.4 接缝端点与跨层覆盖

**定义。** 给定 $e,h\in\mathbb Z$，令

$$
u=\frac{e\alpha-h}{d_L}.
$$

**定理。** 上述 $u$ 满足跨层恒等式

$$
\boxed{
\frac{e\alpha-h}{d_{L+2}}=\frac{u}{\alpha^2},\qquad
\frac{(e+B_L)\alpha-(h+C_L)}{d_{L+1}}
=\frac{1-u}{\alpha}.
}\tag{GC7}
$$

**证明。** 第一式来自 $d_{L+2}=\alpha^2d_L$。第二式使用
$B_L\alpha-C_L=-d_L$ 与 $d_{L+1}=-\alpha d_L$，直接化简即可。

**定理。** 若 $u=\alpha^2$，则接缝唯一落在负返回时刻：

$$
\boxed{e=-F_{L+4}=T_L(-1).}\tag{GC8}
$$

同时 $h=-F_{L+3}$。

**证明。** 将 $u=\alpha^2$ 代入定义，并用 Fibonacci 黄金误差恒等式化简，得到

$$
(e+F_{L+4})\alpha=h+F_{L+3}.
$$

$\alpha$ 无理，故等式两侧的整数系数分别为零，从而得到 $e,h$ 的值。
又因 $\lfloor-\alpha\rfloor=-1$，

$$
T_L(-1)=-A_L-B_L=-F_{L+4}.
$$

**定理。** 对每个 $e\in\mathbb Z$ 且 $e\ne-F_{L+4}$，有接缝外的分辨率覆盖

$$
\boxed{
\operatorname{Hits}_L(e)
\iff\operatorname{Hits}_{L+2}(e)
\ \lor\ \operatorname{Hits}_{L+1}(e+B_L).
}\tag{GC9}
$$

特别地，该等价式对每个 $e\ge0$ 成立。

**证明。** 取 $\operatorname{Hits}_L(e)$ 的见证 $h$ 及其参数 $u\in(0,1)$。
若 $u<\alpha^2$，GC7 第一式给出 $\operatorname{Hits}_{L+2}(e)$；
若 $u>\alpha^2$，GC7 第二式给出
$\operatorname{Hits}_{L+1}(e+B_L)$。等号情形由 GC8 恰为被排除的
$e=-F_{L+4}$。反向地，第一种窗口经 $u=\alpha^2v$ 回到
$u\in(0,\alpha^2)$；第二种窗口经 $u=1-\alpha v$ 回到
$u\in(\alpha^2,1)$。因此两者都推出 $\operatorname{Hits}_L(e)$。
最后 $F_{L+4}>0$，所以 $e\ge0$ 自动避开接缝。

### 8.5 嵌套返回的组合与定向进位

**定义。** 令

$$
c_L=\begin{cases}0,&d_L>0,\\1,&d_L<0.\end{cases}
$$

**命题。** $c_0=0$、$c_{L+1}=1-c_L$；等价地，$L$ 为偶数时
$c_L=0$，$L$ 为奇数时 $c_L=1$。

**证明。** $d_L=(-\alpha)^{L+2}\ne0$，且相邻两层符号相反。

**定理。** 对每个 $m\in\mathbb Z\setminus\{0\}$，

$$
\boxed{
\lfloor T_L(m)\alpha\rfloor
=B_Lm+C_L\lfloor m\alpha\rfloor-c_L.
}\tag{GC10}
$$

**证明。** 令 $k=\lfloor m\alpha\rfloor$。GC1 给出

$$
T_L(m)\alpha-(B_Lm+C_Lk)=d_L(m\alpha-k).
$$

无理性保证 $0<m\alpha-k<1$。若 $d_L>0$，右端严格位于 $(0,1)$；
若 $d_L<0$，右端严格位于 $(-1,0)$。分别取整即得所述修正项。

**定理。** 完整格点变换满足

$$
\boxed{M_KM_L=M_{K+L+2}.}
$$

**证明。** 由 $M_J=Q^{J+2}$，有
$M_KM_L=Q^{K+2}Q^{L+2}=Q^{K+L+4}=M_{K+L+2}$。

**定理。** 对 $m\in\mathbb Z\setminus\{0\}$，嵌套返回满足

$$
\boxed{
T_K(T_L(m))=T_{K+L+2}(m)-B_Kc_L.
}\tag{GC11}
$$

因而

$$
\boxed{
T_K(T_L(m))-T_L(T_K(m))=B_Lc_K-B_Kc_L.
}\tag{GC12}
$$

**证明。** 将 GC10 给出的
$\lfloor T_L(m)\alpha\rfloor$ 代入 $T_K(T_L(m))$，再使用
$M_KM_L=M_{K+L+2}$，得到 GC11。交换 $K,L$ 后两式相减，得到 GC12。

**命题。** GC12 的右端与非零输入 $m$ 无关。两层均为偶数时返回映射交换；
一奇一偶时缺陷非零；两层均为奇数时缺陷为 $B_L-B_K$。
此外 $T_L(0)=0$，但 GC11 的公式不把 $m=0$ 包含在内。

**证明。** 将 $c_J=0$ 或 $1$ 代入 GC12 即得前三项。
$B_J=F_{J+2}>0$ 给出一奇一偶时的非零性。最后由定义直接得到 $T_L(0)=0$。

### 8.6 区间 Fourier 积分的反射与平移

**定义。** 固定实数 $\omega\ne0$。对 $a,b\in\mathbb R$，采用负指数和定向积分约定，定义

$$
\mathcal F_\omega(a,b)=\int_a^b e^{-i\omega x}\,dx.
$$

**定理。** 对所有 $a,b,t\in\mathbb R$，

$$
\boxed{
\mathcal F_\omega(-b,-a)=\overline{\mathcal F_\omega(a,b)},\qquad
|\mathcal F_\omega(-b,-a)|^2=|\mathcal F_\omega(a,b)|^2,
}\tag{GC13}
$$

并且

$$
\boxed{
\mathcal F_\omega(a+t,b+t)
=e^{-i\omega t}\mathcal F_\omega(a,b).
}
$$

**证明。** 当 $\omega\ne0$ 时，端点公式为

$$
\mathcal F_\omega(a,b)=\frac{e^{-i\omega b}-e^{-i\omega a}}{-i\omega}.
$$

把 $(a,b)$ 换成 $(-b,-a)$，并用
$\overline{e^{-i\theta}}=e^{i\theta}$，得到反射取共轭；取模平方得到功率相等。
把端点同时平移 $t$，公因子 $e^{-i\omega t}$ 提出后得到平移公式。

**定义。** 对 $z,w\in\mathbb C$ 定义交叉系数
$\mathcal C(z,w)=z\overline w$。令

$$
z_t=e^{-i\omega t}z,\qquad w_t=e^{-i\omega t}w,\qquad
z^{\mathrm{mir}}=\overline z,\qquad w^{\mathrm{mir}}=\overline w.
$$

**定理。** 共同平移不改变交叉系数，共同反射则使它取共轭；特别地，

$$
\boxed{
\mathcal C(z_t,w_t)=\mathcal C(z,w),\qquad
\operatorname{Im}\mathcal C(z^{\mathrm{mir}},w^{\mathrm{mir}})
=-\operatorname{Im}\mathcal C(z,w).
}\tag{GC14}
$$

**证明。** 直接计算得
$z_t\overline{w_t}=e^{-i\omega t}z\,e^{i\omega t}\overline w=z\overline w$，
而
$\mathcal C(\overline z,\overline w)=\overline z\,w
=\overline{z\overline w}$。取虚部即得第二式。

**命题。** 若 $\mathcal C(z,w)$ 为零或实数，则共同反射前后的交叉系数虚部都为零。

**证明。** 实数等于自身的共轭，且实数的虚部为零；零是其实例。

### 8.7 有限载体与 Fibonacci 窗口

**定义。** 令

$$
R=\{0,1,2,3,4\}\times\{0,1,2\}\times\{0,1\}\times\{0,1\},
$$

$$
W_n=\{0,1\}^n,
\qquad
X_n=\{w\in W_n: w_jw_{j+1}=0\text{ 对所有 }1\le j<n\}.
$$

**命题。** 有

$$
|R|=60,\qquad |W_6|=64,\qquad |X_6|=21,\qquad
|W_6\setminus X_6|=43.
$$

此外 $|X_7|=34$、$|X_8|=55$，所以
$|X_8|-|X_6|=34\ne43$。

**证明。** 前两个基数由有限集合乘法原则得到。
令 $x_n=|X_n|$。按末位为 $0$ 或 $1$ 分拆合法字，得到
$x_n=x_{n-1}+x_{n-2}$，且 $x_1=2$、$x_2=3$。
递推给出 $x_6=21$、$x_7=34$、$x_8=55$，其余等式随即成立。

**定理。** 映射

$$
\rho(x,y,z,w)=12x+4y+2z+w
$$

是 $R$ 到 $\{0,1,\ldots,59\}$ 的双射。把值写成六位二进制时，
$W_6$ 中恰有 $60,61,62,63$ 四个码不在像中。

**证明。** 对 $r\in\{0,\ldots,59\}$，依次令

$$
w=r\bmod2,\qquad
z=\lfloor r/2\rfloor\bmod2,\qquad
y=\lfloor r/4\rfloor\bmod3,\qquad
x=\lfloor r/12\rfloor.
$$

这些值属于 $R$ 的相应因子，连续使用带余除法可恢复
$r=12x+4y+2z+w$，且恢复唯一。六位二进制编码覆盖 $0$ 至 $63$，
故像的补集恰为所列四个码。

### 8.8 不同分辨率中心的共同反射阻碍

**定义。** 第 $L$ 层有符号区间的中心记为

$$
\mu_L=\frac{d_L}{2}.
$$

**定理。** 若 $r\in\mathbb N$ 且 $r>0$，则不存在 $t\in\mathbb R$ 同时满足

$$
\mu_L+t=-\mu_L,\qquad
\mu_{L+r}+t=-\mu_{L+r}.
$$

**证明。** 两式分别给出 $t=-d_L$ 与 $t=-d_{L+r}$，从而要求
$D_{L,r}=d_L-d_{L+r}=0$，这与 GC5 矛盾。

**定理。** 若 $\omega\ne0$，且 $r\in\mathbb N$、$r>0$，则未取模的几何相位差

$$
\Theta_{L,r}=-\frac{\omega}{2}(d_L-d_{L+r})
$$

满足

$$
\boxed{\Theta_{L,r}\ne0,\qquad
\Theta_{L+1,r}=-\alpha\Theta_{L,r}.}
$$

**证明。** 非零性由 $\omega\ne0$ 与 GC5 得到；递推式由
$D_{L+1,r}=-\alpha D_{L,r}$ 得到。

**命题。** 对实数 $\theta$，条件 $\theta\ne0$ 本身不推出
$e^{i\theta}\ne1$。

**证明。** 取 $\theta=2\pi$，则 $\theta\ne0$，但
$e^{i\theta}=e^{2\pi i}=1$。

### 8.9 有限基数与黄金回归的分离

**命题。** 整数 $60$ 与 $64$ 都不是黄金旋转
$x\mapsto x+\alpha\pmod1$ 的回归周期。

**证明。** 两数均非零，故 GC6 分别给出
$60\alpha\notin\mathbb Z$ 与 $64\alpha\notin\mathbb Z$。

**命题。** 六位二进制字中不满足无相邻 $1$ 条件的字数为 $43$，
而 $|X_7|=|X_8|-|X_6|=34$；这两个计数不相等。

**证明。** 由 8.7 的递推计数，二者之差为 $43-34=9\ne0$。

---

## 9. 整数纤维、截面依赖与规范双面的乘法作用

### 9.1 黄金整数及其两个实嵌入

**定义。** 令

$$
\mathcal O=\mathbb Z[\varphi]
=\{a+b\varphi:a,b\in\mathbb Z\},
\qquad \varphi^2=\varphi+1.
$$

对 $z=a+b\varphi\in\mathcal O$，定义两个实嵌入及整数坐标读出

$$
z_+=a+b\varphi,
\qquad z_*=a+b\psi,
\qquad \pi(z)=b,
$$

其中 $\psi=-\alpha$ 且 $\psi^2=\psi+1$。

**定理。** 两个嵌入都保持加法与乘法，并且

$$
\boxed{z_+-z_*=\sqrt5\,\pi(z).}
$$

**证明。** 加法保持性直接来自坐标相加。因为 $\varphi$ 与 $\psi$
都满足 $x^2=x+1$，按该关系展开两个乘积即可得到乘法保持性。
又有 $\varphi-\psi=1+2\alpha=\sqrt5$，故
$z_+-z_*=b(\varphi-\psi)=\sqrt5\,b$。

### 9.2 完整整数纤维与乘法不下降

**定理。** 对每个 $n\in\mathbb Z$，完整纤维为

$$
\boxed{\pi^{-1}(n)=\{k+n\varphi:k\in\mathbb Z\}.}\tag{GS1}
$$

此外，$\pi(x)=\pi(y)$ 当且仅当存在 $k\in\mathbb Z$ 使 $y=x+k$。

**证明。** 写 $z=a+b\varphi$，则 $\pi(z)=n$ 等价于 $b=n$，
此时且仅此时 $z=a+n\varphi$。对 $x,y$ 应用同一坐标比较即得后一结论。

**定理。** 令 $u=c+d\varphi\in\mathcal O$。对任意 $k,n\in\mathbb Z$，

$$
\pi\bigl(u(k+n\varphi)\bigr)=(c+d)n+dk.
$$

并且乘法在整数纤维上下降为单值映射的充要条件是 $u$ 为普通整数：

$$
\boxed{
\exists f:\mathbb Z\to\mathbb Z\ \forall z\in\mathcal O,
\quad \pi(uz)=f(\pi z)
\quad\Longleftrightarrow\quad d=0.
}\tag{GS2}
$$

**证明。** 展开
$u(k+n\varphi)$ 并使用 $\varphi^2=\varphi+1$，其 $\varphi$ 坐标即为
$(c+d)n+dk$。若 $d=0$，取 $f(n)=cn$ 即可。反之，$0$ 与 $1$
同属零纤维，而其乘积读出分别为 $0$ 与 $d$；单值性强制 $d=0$。

**定理。** 若 $d\ne0$，则对每个固定的 $n$，映射

$$
k\longmapsto\pi\bigl(u(k+n\varphi)\bigr)
$$

是单射，因此每个纤维产生无限多个不同的一步输出。此时联合读出

$$
\boxed{z\longmapsto(\pi z,\pi(uz))\text{ 是单射}.}\tag{GS3}
$$

**证明。** 固定 $n$ 后，输出是斜率为非零整数 $d$ 的仿射函数，故对
$k$ 单射。若联合读出相等，第一坐标先确定相同的 $n$，第二坐标再由该单射
确定相同的 $k$；GS1 遂给出相同的 $z$。

### 9.3 任意截面的进位与复合缺陷

**定义。** 对 $\rho\in\mathbb R$ 与 $n\in\mathbb Z$，定义

$$
q_\rho(n)=\lfloor n\alpha+\rho\rfloor,
\qquad s_\rho(n)=q_\rho(n)+n\varphi,
\qquad r_\rho(n)=n\alpha-q_\rho(n).
$$

若 $u=a_u+b_u\varphi$，再定义

$$
P_u^\rho(n)=\pi(u s_\rho(n)),
$$

并在写成 $u s_\rho(n)=A+P_u^\rho(n)\varphi$ 后定义

$$
c_u^\rho(n)=q_\rho(P_u^\rho(n))-A.
$$

**命题。** $s_\rho$ 是 $\pi$ 的一个截面，并且

$$
\pi(s_\rho(n))=n,
\qquad -\rho\le r_\rho(n)<1-\rho,
\qquad (s_\rho(n))_*=-r_\rho(n).
$$

**证明。** 第一式由 $s_\rho(n)$ 的 $\varphi$ 坐标得到。
取整的基本界给出第二式，而
$q_\rho(n)+n\psi=q_\rho(n)-n\alpha=-r_\rho(n)$ 给出第三式。

**定理。** 对任意 $u\in\mathcal O$、$\rho\in\mathbb R$ 与
$n\in\mathbb Z$，截面进位满足

$$
\boxed{
c_u^\rho(n)=\lfloor u_*r_\rho(n)+\rho\rfloor,
\qquad
s_\rho(P_u^\rho(n))=u s_\rho(n)+c_u^\rho(n).
}\tag{GS4}
$$

**证明。** 写 $u s_\rho(n)=A+P\varphi$，其中 $P=P_u^\rho(n)$。
取内部嵌入并用 $(s_\rho(n))_*=-r_\rho(n)$，得到
$A-P\alpha=-u_*r_\rho(n)$，即 $P\alpha=A+u_*r_\rho(n)$。
因此

$$
c_u^\rho(n)=\lfloor P\alpha+\rho\rfloor-A
=\lfloor u_*r_\rho(n)+\rho\rfloor.
$$

第二式比较整数坐标与 $\varphi$ 坐标即可。

**定理。** 对所有 $u,v\in\mathcal O$、$\rho\in\mathbb R$ 与
$n\in\mathbb Z$，

$$
\boxed{
P_u^\rho(P_v^\rho(n))
=P_{uv}^\rho(n)+b_u c_v^\rho(n),
}\tag{GS5}
$$

$$
\boxed{
P_u^\rho(P_v^\rho(n))-P_v^\rho(P_u^\rho(n))
=b_u c_v^\rho(n)-b_v c_u^\rho(n).
}\tag{GS6}
$$

**证明。** 由 GS4，
$s_\rho(P_v^\rho(n))=v s_\rho(n)+c_v^\rho(n)$。
两边乘以 $u$ 后取 $\varphi$ 坐标，注意普通整数
$c_v^\rho(n)$ 乘以 $u$ 所贡献的 $\varphi$ 坐标为
$b_uc_v^\rho(n)$，便得到 GS5。交换 $u,v$，再用 $uv=vu$ 相减，得到 GS6。

### 9.4 中心截面的乘法不变性

**定理。** 对每个 $n\in\mathbb Z$，

$$
|r_{1/2}(n)|<\frac12.
$$

若 $u\in\mathcal O$ 且 $|u_*|\le1$，则

$$
\boxed{
c_u^{1/2}(n)=0,
\qquad
s_{1/2}(P_u^{1/2}(n))=u s_{1/2}(n).
}\tag{GS7}
$$

**证明。** 取整界先给出 $|r_{1/2}(n)|\le1/2$。
若出现端点，则 $n\alpha$ 为半整数；当 $n\ne0$ 时这与 $\alpha$ 无理矛盾，
而 $n=0$ 时 $r_{1/2}(0)=0$。故不等式严格。
于是 $|u_*r_{1/2}(n)|<1/2$，从而
$u_*r_{1/2}(n)+1/2\in(0,1)$。GS4 的取整公式给出进位为零，
再由 GS4 的第二式得到截面不变性。

**定理。** 集合

$$
\mathcal C=\{u\in\mathcal O:|u_*|\le1\}
$$

对乘法闭合。若 $u_1,\ldots,u_t\in\mathcal C$，则

$$
\boxed{
P_{u_1}^{1/2}\cdots P_{u_t}^{1/2}(n)
=P_{u_1\cdots u_t}^{1/2}(n).
}\tag{GS8}
$$

特别地，这些投影映射两两交换。

**证明。** 乘法嵌入给出
$(uv)_*=u_*v_*$，所以 $|u_*|,|v_*|\le1$ 推出 $|(uv)_*|\le1$。
对字长归纳，并在每一步使用 GS7，即得 GS8。环乘法交换律再给出投影映射的交换性。

### 9.5 全部分辨率共同不变窗口的锐利范围

**定义。** 对 $0\le\rho\le1$，令

$$
W_\rho=[-\rho,1-\rho]\subset\mathbb R.
$$

**定理。** 对 $d_L=\psi^{L+2}$，全部分辨率共同保持 $W_\rho$ 的充要条件是

$$
\boxed{
\forall L\in\mathbb N,\ d_LW_\rho\subseteq W_\rho
\quad\Longleftrightarrow\quad
\frac{1-\alpha}{2}\le\rho\le\frac{1+\alpha}{2}.
}\tag{GS9}
$$

若 $\rho$ 超出该闭区间，则 $L=1$ 的负收缩已经不保持 $W_\rho$。

**证明。** 每个正向 $d_L$ 都是不超过 $\alpha^2$ 的正收缩，因而保持
包含零的 $W_\rho$。对 $q>0$，负收缩 $-q$ 的像为

$$
[-q(1-\rho),q\rho],
$$

故它包含于 $W_\rho$ 当且仅当

$$
q(1-\rho)\le\rho,
\qquad q\rho\le1-\rho.
$$

最大的负向绝对值出现在 $L=1$，此时 $q=\alpha^3$；其余负向层再乘
$\alpha^2$，所以只需检验这一层。代入 $q=\alpha^3=2\alpha-1$，
两条不等式分别化为
$\rho\ge(1-\alpha)/2$ 与 $\rho\le(1+\alpha)/2$。
超出范围时，相应端点在 $L=1$ 即越出窗口。

### 9.6 规范黄金截面与返回锚定

**定义。** 对 $n\in\mathbb N$，令

$$
S(n)=\lfloor(n+1)\varphi\rfloor-1,
\qquad
\beta_{\mathbb R}(n)=S(n)-n\psi,
$$

并定义规范黄金整数

$$
\beta_{\mathrm G}(n)=(S(n)-n)+n\varphi\in\mathcal O.
$$

**定理。** 规范黄金整数恰好是偏移为 $\alpha$ 的截面：

$$
\boxed{
\beta_{\mathrm G}(n)=s_\alpha(n)
=\lfloor(n+1)\alpha\rfloor+n\varphi.
}\tag{GS10}
$$

其正实嵌入为 $\beta_{\mathbb R}(n)$，内部实嵌入为
$(\beta_{\mathrm G}(n))_*$。

**证明。** 因为 $\varphi=1+\alpha$，

$$
S(n)=n+\lfloor(n+1)\alpha\rfloor.
$$

代回定义便得到 GS10。正实嵌入满足

$$
(S(n)-n)+n\varphi=S(n)+n\alpha=S(n)-n\psi
=\beta_{\mathbb R}(n),
$$

内部嵌入则由定义直接得到。

**定义。** 对 $L\in\mathbb N$，令

$$
u_L=\varphi^{L+2},
\qquad U_L(n)=P_{u_L}^{\alpha}(n)\quad(n\in\mathbb Z).
$$

**定理。** 对每个 $L$ 与 $n\in\mathbb Z$，规范截面的进位为零，且

$$
s_\alpha(U_L(n))=u_Ls_\alpha(n).
$$

因此

$$
\boxed{U_K(U_L(n))=U_{K+L+2}(n).}\tag{GS11}
$$

若 $n\in\mathbb N$，则 $U_L(n)\ge0$，并且把该输出视为自然数时，

$$
\boxed{
\beta_{\mathrm G}(U_L(n))
=\varphi^{L+2}\beta_{\mathrm G}(n).
}\tag{GS12}
$$

**证明。** 由取整界，
$r_\alpha(n)\in[-\alpha,1-\alpha)$。将该半开区间乘以
$d_L=(u_L)_*$；利用 $|d_L|<1$、符号交替及无理性排除可能的整数端点，得到

$$
0\le d_Lr_\alpha(n)+\alpha<1.
$$

GS4 因而给出零进位与截面不变性。又因
$u_Ku_L=u_{K+L+2}$，连续应用截面不变性并取 $\pi$，得到 GS11。
对自然数 $n$，$s_\alpha(n)$ 的两个整数坐标非负，而
$u_L=F_{L+1}+F_{L+2}\varphi$ 的两个坐标也非负，故乘积的
$\varphi$ 坐标 $U_L(n)$ 非负。最后结合 GS10 与截面不变性得到 GS12。

**定理。** 第 8 节的返回映射与规范尺度映射满足锚定关系

$$
\boxed{T_L(m)=A_L+U_L(m-1),\qquad m\in\mathbb Z.}\tag{GS13}
$$

**证明。** 由
$u_L=F_{L+1}+F_{L+2}\varphi=C_L+B_L\varphi$，且

$$
q_\alpha(m-1)=\lfloor m\alpha\rfloor,
$$

展开 $u_Ls_\alpha(m-1)$ 的 $\varphi$ 坐标，得到

$$
U_L(m-1)=A_L(m-1)+B_L\lfloor m\alpha\rfloor
=T_L(m)-A_L.
$$

移项即得 GS13。

### 9.7 加法截面的乘法不变性阻碍

**定理。** 设 $s:\mathbb Z\to\mathcal O$ 是加法同态，且

$$
\pi(s(n))=n\qquad(n\in\mathbb Z).
$$

若 $u=c+d\varphi$ 且 $d\ne0$，则

$$
\boxed{
\neg\,\forall n\in\mathbb Z,
\quad u s(n)=s(\pi(u s(n))).
}\tag{GS14}
$$

**证明。** 由截面条件可写 $s(1)=a+\varphi$，其中 $a\in\mathbb Z$。
加法性给出 $s(n)=n(a+\varphi)$。若所述不变性成立，将 $n=1$ 代入，
并比较 $u(a+\varphi)$ 与 $s(\pi(u(a+\varphi)))$ 的两个整数坐标，得到

$$
d(a^2+a-1)=0.
$$

因 $d\ne0$，必有 $a(a+1)=1$；但两个相邻整数之积为偶数，不可能等于
$1$，矛盾。

### 9.8 返回映射与规范尺度不存在共同单射共轭

**定理。** 若 $B_Lc_K-B_Kc_L\ne0$，则不存在单射
$f:\mathbb Z\to\mathbb Z$ 同时满足

$$
f\circ T_K=U_K\circ f,
\qquad
f\circ T_L=U_L\circ f.
$$

**证明。** GS11 给出 $U_KU_L=U_LU_K$。若这样的 $f$ 存在，
则对任意非零 $m$，连续使用两条交织关系得到

$$
f(T_K(T_L(m)))=U_K(U_L(f(m)))
=U_L(U_K(f(m)))=f(T_L(T_K(m))).
$$

$f$ 的单射性迫使 $T_K(T_L(m))=T_L(T_K(m))$，
这与 GC12 及 $B_Lc_K-B_Kc_L\ne0$ 矛盾。

### 9.9 三种截面性质的分离

**定理。** 设 $u=c+d\varphi\in\mathcal O$ 满足 $d\ne0$ 且
$|u_*|\le1$。则下列三项同时成立：乘法 $z\mapsto uz$ 不下降为完整
$\pi$-纤维上的单值映射；中心截面 $s_{1/2}(\mathbb Z)$ 在该乘法下不变；
不存在既为加法同态又在该乘法下不变的 $\pi$-截面。

**证明。** 第一项由 GS2 与 $d\ne0$ 得到，第二项由 GS7 与
$|u_*|\le1$ 得到，第三项由 GS14 得到。
## 附录 T：WSS 的素数下标迹障碍与幂复合多项式

### T.1 黄金整数环、迹与范数

**定义。** 令

$$
\varphi=\frac{1+\sqrt5}{2},
\qquad \psi=1-\varphi=\frac{1-\sqrt5}{2},
\qquad \mathcal O=\mathbb Z[\varphi].
$$

对 $z=a+b\varphi\in\mathcal O$，定义

$$
\overline z=a+b\psi,
\qquad \operatorname{Tr}(z)=z+\overline z,
\qquad \operatorname N(z)=z\overline z.
$$

**定义。** Lucas 数与 Fibonacci 数分别由

$$
L_n=\varphi^n+\psi^n,
\qquad
F_n=\frac{\varphi^n-\psi^n}{\sqrt5}
$$

定义。

**定理。** 对每个 $n\in\mathbb N$，

$$
\varphi^2=\varphi+1,
\qquad \varphi\psi=-1,
\qquad \operatorname N(\varphi^n)=(-1)^n.
$$

**证明。** 前两式由 $\varphi=(1+\sqrt5)/2$ 与
$\psi=(1-\sqrt5)/2$ 直接计算得到。由范数的乘法性，

$$
\operatorname N(\varphi^n)
=(\varphi\psi)^n=(-1)^n.
$$

### T.2 幂复合多项式与整数环指数

**定义。** 对 $n\in\mathbb N$，定义

$$
\mathcal P_n(X)=X^{2n}-X^n-1,
\qquad E_n=\mathcal P_n(\varphi)\in\mathcal O.
$$

**定义。** 设 $p$ 为奇素数，$\theta_p$ 是 $\mathcal P_p$ 的一个根，
$K_p=\mathbb Q(\theta_p)$，而 $\mathcal O_{K_p}$ 是 $K_p$ 的整数环。
当 $\mathcal P_p$ 是 $\theta_p$ 的最小多项式时，定义指定幂基的指数为

$$
I_p=[\mathcal O_{K_p}:\mathbb Z[\theta_p]].
$$

指定幂基是整数环的整基，依定义即为 $I_p=1$。

**定理。** 对每个奇素数 $p$，

$$
\operatorname{disc}(\mathcal P_p)=p^{2p}5^p.
$$

若 $\mathcal P_p$ 是 $\theta_p$ 的最小多项式，则

$$
\operatorname{disc}(\mathcal P_p)
=I_p^2\operatorname{disc}(K_p).
$$

**证明。** 导数为

$$
\mathcal P_p'(X)=pX^{p-1}(2X^p-1).
$$

以 $Y=X^p$ 计算两个结果式，得到

$$
\operatorname{Res}(\mathcal P_p,X^{p-1})=1,
\qquad
\operatorname{Res}(\mathcal P_p,2X^p-1)=-5^p.
$$

由于 $\deg\mathcal P_p=2p$ 且 $p$ 为奇数，判别式与结果式的符号相消，
从而得到第一式。第二式是基变换的判别式公式：
$\mathbb Z[\theta_p]$ 到 $\mathcal O_{K_p}$ 的基变换行列式绝对值为 $I_p$，
而判别式在基变换下乘以该行列式的平方。

### T.3 奇数下标的迹恒等式

**定理。** 对每个奇数 $n$，

$$
\boxed{E_n=(L_n-1)\varphi^n.}\tag{T1}
$$

**证明。** 每个二次元素 $x\in\mathcal O$ 满足

$$
x^2-\operatorname{Tr}(x)x+\operatorname N(x)=0,
$$

因为左端展开为
$x^2-(x+\overline x)x+x\overline x=0$。取 $x=\varphi^n$。
此时 $\operatorname{Tr}(x)=L_n$；又因 $n$ 为奇数，
$\operatorname N(x)=-1$。因此

$$
E_n=x^2-x-1=(\operatorname{Tr}(x)-1)x
=(L_n-1)\varphi^n.
$$

### T.4 标量整除、模同余与范数

**定理。** 对每个奇数 $n$ 与每个整数 $q$，

$$
\boxed{q\mid E_n\text{ 于 }\mathcal O
\iff q\mid L_n-1\text{ 于 }\mathbb Z.}\tag{T2}
$$

这包括复合整数 $q$ 及 $q=0$。

**证明。** 令 $x=\varphi^n$。由
$x\overline x=-1$ 可知 $x^{-1}=-\overline x\in\mathcal O$。
若 $E_n=qy$，则 T1 给出

$$
L_n-1=qyx^{-1}.
$$

写 $yx^{-1}=a+b\varphi$。比较 $\{1,\varphi\}$ 中的整数坐标可得
$b=0$ 及 $L_n-1=qa$。反之，若 $L_n-1=qa$，则
$E_n=q(a\varphi^n)$。上述论证也适用于 $q=0$。

**定理。** 对每个奇数 $n$ 与每个自然数 $q$，

$$
\boxed{E_n\equiv0\pmod q\text{ 于 }\mathcal O
\iff L_n\equiv1\pmod q\text{ 于 }\mathbb Z.}\tag{T3}
$$

**证明。** 两个同余分别等价于 $q\mid E_n$ 于 $\mathcal O$ 与
$q\mid L_n-1$ 于 $\mathbb Z$，故结论由 T2 得到。

**定理。** 对每个奇数 $n$，

$$
\boxed{\operatorname N(E_n)=-(L_n-1)^2.}\tag{T4}
$$

**证明。** 由 T1、范数的乘法性及
$\operatorname N(\varphi^n)=-1$，有

$$
\operatorname N(E_n)
=\operatorname N(L_n-1)\operatorname N(\varphi^n)
=(L_n-1)^2(-1).
$$

### T.5 素数平方特化与规范化周期商

**定义。** 对奇素数 $p\ne5$，令

$$
\epsilon=\left(\frac5p\right),
\qquad m=p-\epsilon.
$$

在下述整除性成立时，定义规范化商

$$
\ell_p=\frac{L_p-1}{p}\pmod p,
\qquad q_p=\frac{F_m}{p}\pmod p.
$$

**定理。** 对每个奇素数 $p\ne5$，有

$$
p\mid L_p-1,
\qquad p\mid F_{p-\epsilon},
\qquad 2\ell_p=5q_p\pmod p.
$$

**证明。** 在 $\mathbb F_p[\sqrt5]$ 中，Euler 判据与 Frobenius 映射给出

$$
(\sqrt5)^p=\epsilon\sqrt5,
\qquad L_p\equiv1\pmod p,
\qquad F_p\equiv\epsilon\pmod p.
$$

由
$L_p=F_p+2F_{p-1}=2F_{p+1}-F_p$，得到
$p\mid F_{p-\epsilon}$。写

$$
F_p=\epsilon+pA,
\qquad F_{p-\epsilon}=pB.
$$

若 $\epsilon=1$，Cassini 恒等式化为

$$
F_p^2-F_pF_{p-1}-F_{p-1}^2=1.
$$

模 $p^2$ 化简得 $2A\equiv B\pmod p$，而
$\ell_p\equiv A+2B$、$q_p\equiv B$，所以
$2\ell_p\equiv5q_p\pmod p$。若 $\epsilon=-1$，Cassini 恒等式化为

$$
F_{p+1}(F_{p+1}-F_p)-F_p^2=-1.
$$

模 $p^2$ 化简得 $2A\equiv-B\pmod p$，而
$\ell_p\equiv2B-A$、$q_p\equiv B$，仍有
$2\ell_p\equiv5q_p\pmod p$。

**定义。** 奇素数 $p$ 称为 WSS 素数，当且仅当

$$
p^2\mid L_p-1.
$$

**定理。** 对每个奇素数 $p$，

$$
\boxed{
p^2\mid\mathcal P_p(\varphi)\text{ 于 }\mathcal O
\iff p^2\mid L_p-1\text{ 于 }\mathbb Z.
}
$$

并且

$$
\operatorname N(\mathcal P_p(\varphi))=-(L_p-1)^2.
$$

若 $p\ne5$，上述条件还等价于
$\ell_p=0$，也等价于 $q_p=0$。

**证明。** 取 $n=p$、$q=p^2$ 代入 T2，得到第一组等价；取
$n=p$ 代入 T4，得到范数公式。最后，
$p^2\mid L_p-1$ 当且仅当 $\ell_p=0$；由于 $2$ 与 $5$ 在
$\mathbb F_p$ 中均可逆，等式 $2\ell_p=5q_p$ 又给出
$\ell_p=0\iff q_p=0$。

### T.6 两个实嵌入下的取值

**定义。** 定义 $\mathcal O$ 的两个实嵌入

$$
\sigma_+(a+b\varphi)=a+b\varphi,
\qquad
\sigma_*(a+b\varphi)=a+b\psi.
$$

**定理。** 对每个奇数 $n$，

$$
\sigma_+(E_n)=(L_n-1)\varphi^n,
\qquad
\sigma_*(E_n)=(L_n-1)\psi^n,
$$

并且两个实嵌入值的乘积为

$$
\sigma_+(E_n)\sigma_*(E_n)=-(L_n-1)^2.
$$

**证明。** 对 T1 分别应用 $\sigma_+$ 与 $\sigma_*$，得到前两式。
再使用 $\varphi\psi=-1$ 及 $n$ 为奇数，得到

$$
\sigma_+(E_n)\sigma_*(E_n)
=(L_n-1)^2(\varphi\psi)^n
=-(L_n-1)^2.
$$

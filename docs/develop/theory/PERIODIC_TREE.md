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

## 附录 R：Fibonacci 回归谱与素数幂提升

### R.1 Fibonacci 矩阵与黄金二次环

**定义。** 令 $F_0=0$、$F_1=1$、$F_{t+2}=F_{t+1}+F_t$，并令

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad \det Q=-1,
\qquad \mathcal O=\mathbb Z[\varphi],\quad \varphi^2=\varphi+1.
$$

**命题。** Fibonacci 矩阵满足

$$
Q^2=
\begin{pmatrix}1&1\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

**证明。** 两端直接相乘都等于 $\begin{pmatrix}2&1\\1&1\end{pmatrix}$。

**定理。** 对全部 $t\ge0$，

$$
\boxed{
Q^t=
\begin{pmatrix}
F_{t+1}&F_t\\F_t&F_{t+1}-F_t
\end{pmatrix}.}
\tag{R1}
$$

**证明。** 当 $t=0$ 时右端是单位矩阵。若公式对 $t$ 成立，将右端乘以
$Q$，再用 $F_{t+2}=F_{t+1}+F_t$，便得到 $t+1$ 时的公式。

### R.2 序列周期、伴随矩阵阶与黄金单位阶

**定义。** 对正整数 $q$，令 $\pi(q)$ 为 $Q$ 在
$GL_2(\mathbb Z/q\mathbb Z)$ 中的阶；等价地，它是 Fibonacci 递推的可逆伴随矩阵
$\begin{pmatrix}1&1\\1&0\end{pmatrix}$ 的阶。特别地，$\pi(1)=1$。

**定理。** 对正整数 $q$ 与 $t\ge0$，

$$
\boxed{
\pi(q)\mid t
\iff(F_t,F_{t+1})\equiv(0,1)\pmod q
\iff\forall n\ge0,\ F_{n+t}\equiv F_n\pmod q.
}
\tag{R2}
$$

**证明。** 由 R1，$Q^t=I$ 当且仅当矩阵的左下项为 $0$、左上项为
$1$，即 $(F_t,F_{t+1})\equiv(0,1)$。若 $Q^t=I$，则
$Q^{n+t}=Q^n$，比较左下项便得序列同余。反之，在序列同余中依次取
$n=0,1$，即得所需的两项回归条件。

**定义。** 对 $z=a+b\varphi\in\mathcal O/q\mathcal O$，以反序坐标
$(b,a)$ 定义正则表示

$$
\mathcal R_q(z)=\begin{pmatrix}a+b&b\\b&a\end{pmatrix}.
\tag{R3}
$$

**定理。** $\mathcal R_q$ 是单射环同态，$\mathcal R_q(\varphi)=Q$，因而

$$
\boxed{\pi(q)=\operatorname{ord}(\overline\varphi\in(\mathcal O/q\mathcal O)^\times).}
\tag{R4}
$$

**证明。** 若 $w=c+d\varphi$，则
$zw=(ac+bd)+(ad+bc+bd)\varphi$；在坐标 $(d,c)$ 上，这正是 R3 的矩阵作用。
由此乘法与加法均被保持。矩阵第二列为 $(b,a)$，故表示为零只可能
$a=b=0$，所以它单射。取 $z=\varphi$ 得 $Q$；单射同态保持并反映
幂等于单位元，故两侧的阶相等。

### R.3 回归内容量与整除对偶

**定义。** 对 $t\ge0$，定义

$$
C_t=\gcd(F_t,F_{t+1}-1).
$$

**定理。** 对正整数 $q$ 与 $t\ge0$，

$$
\boxed{\pi(q)\mid t\iff q\mid C_t.}
\tag{R5}
$$

**证明。** 由 R2，左侧等价于 $q\mid F_t$ 且
$q\mid(F_{t+1}-1)$；这又等价于 $q$ 整除两数的最大公约数。

**命题。** $C_0=0$；若 $t>0$，则 $C_t>0$，并且满足
$\pi(q)\mid t$ 的正整数 $q$ 恰有 $\tau(C_t)$ 个。

**证明。** 初值得 $C_0=\gcd(0,0)=0$。当 $t>0$ 时，$F_t>0$，故
$C_t>0$。R5 表明所求正整数恰为 $C_t$ 的全部正约数，数量即
$\tau(C_t)$。

**定理。** 对正整数 $a,b$ 与非负整数 $s,t$，

$$
\boxed{
\pi(\operatorname{lcm}(a,b))=\operatorname{lcm}(\pi(a),\pi(b)),\qquad
C_{\gcd(s,t)}=\gcd(C_s,C_t).
}
\tag{R6}
$$

**证明。** 任意 $T$ 同时被 $\pi(a),\pi(b)$ 整除，当且仅当
$a,b$ 同时整除 $C_T$，也即 $\operatorname{lcm}(a,b)\mid C_T$；以
$T$ 取两边相应的最小周期，双向整除即得第一式。对任意正整数 $q$，
$q\mid C_{\gcd(s,t)}$ 当且仅当 $\pi(q)$ 同时整除 $s,t$，也即
$q$ 同时整除 $C_s,C_t$。若 $s=t=0$，第二式由 $C_0=0$ 直接成立；
否则两边均为正整数，分别取 $q$ 为等式两边便得第二式。

### R.4 第六十步回归与三个有限模数

**命题。** 有

$$
C_{60}=832040=2^3\cdot5\cdot11\cdot31\cdot61,
\qquad \tau(C_{60})=64.
$$

**证明。** 用 Fibonacci 递推算出 $F_{60}$ 与 $F_{61}$，再施行欧几里得算法，
得到 $\gcd(F_{60},F_{61}-1)=832040$；所示素因子分解给出
$\tau(C_{60})=(3+1)2^4=64$。

**命题。** 在 $C_{60}$ 的 $64$ 个正约数中，除 $q=1$ 外有 $63$ 个
非平凡模数，并且有 $49$ 个模数满足 $\pi(q)=60$。

**证明。** $64$ 个正约数中只有 $q=1$ 等于 $1$，其余 $63$ 个均大于 $1$。
由 R2 直接计算

$$
\pi(1)=1, \pi(2)=3, \pi(4)=6, \pi(8)=12,
\ \pi(5)=20, \pi(11)=10, \pi(31)=30, \pi(61)=60.
$$

**证明。** 含因子 $61$ 的 $32$ 个约数均有周期 $60$。不含 $61$ 时，周期的最小公倍数
等于 $60$ 的情形按 $2$ 的指数 $3,2,1,0$ 分别有 $7,4,4,2$ 个，合计
$17$ 个。因此总数为 $32+17=49$。

**命题。** 下列数值成立：

| 模数 $N$ | $\tau(N)$ | $\pi(N)$ |
|---|---:|---:|
| $5040=2^4 3^2 5\cdot7$ | 60 | 240 |
| $7560=2^3 3^3 5\cdot7$ | 64 | 720 |
| $55440=2^4 3^2 5\cdot7\cdot11$ | 120 | 240 |

**证明。** 约数个数由三行的素因子指数相乘得到。用 R2 逐次乘矩阵可得

$$
\pi(16)=24,\quad\pi(9)=24,\quad\pi(8)=12,\quad\pi(27)=72,\quad
\pi(5)=20,\quad\pi(7)=16,\quad\pi(11)=10.
$$

**证明。** 再由 R6 对各互素素数幂取周期的最小公倍数，依次得到 $240,720,240$。

### R.5 模平方的平方零回归缺陷与 Wall 二分律

**定义。** 设 $p>0$，$r=\pi(p)$，并定义整数

$$
a=F_r/p,\qquad b=(F_{r+1}-1)/p,\qquad
B=\begin{pmatrix}b&a\\a&b-a\end{pmatrix}.
$$

**证明。** 这些商为整数，因为 R2 给出 $p\mid F_r$ 与 $p\mid(F_{r+1}-1)$。

**定理。** 在 $\mathbb Z/p^2\mathbb Z$ 上，

$$
\boxed{Q^r=I+pB.}
\tag{R7}
$$

**证明。** 将 $F_r=pa$ 与 $F_{r+1}=1+pb$ 代入 R1 的四个矩阵项即可。

**定理。** 若环中 $D^2=0$，则对全部 $m\ge0$，

$$
(1+D)^m=1+mD.
$$

**证明。** 对 $m$ 归纳。归纳步中
$(1+mD)(1+D)=1+(m+1)D+mD^2=1+(m+1)D$。

**定理。** 对任意正整数 $p$，

$$
\pi(p)\mid\pi(p^2)\mid p\pi(p).
$$

**证明。** 降模同态给出左侧整除。令 $D=pB$；在模 $p^2$ 下有
$D^2=0$ 与 $pD=0$。由 R7 和前一定理，
$(Q^r)^p=(I+D)^p=I+pD=I$，故 $\pi(p^2)\mid pr$。

**定理。** 若 $p$ 为素数，则下列二者必有且仅有一个成立；该结论包括
$p=2$ 与 $p=5$：

$$
\boxed{\pi(p^2)=\pi(p)\quad\text{或}\quad
\pi(p^2)=p\pi(p).}
\tag{R8}
$$

**证明。** 由前一定理，$\pi(p^2)/\pi(p)$ 是 $p$ 的正约数；素性迫使它
等于 $1$ 或 $p$。

**定理。** 对素数 $p$，

$$
\boxed{
\pi(p^2)=\pi(p)
\iff p^2\mid C_{\pi(p)}
\iff p\mid a\ \text{且}\ p\mid b.
}
\tag{R9}
$$

**证明。** 第一处等价由 R5 对旧周期与模 $p^2$ 应用，并结合
$\pi(p)\mid\pi(p^2)$。又因 $F_r=pa$、$F_{r+1}-1=pb$，
$p^2$ 同时整除这两数当且仅当 $p$ 同时整除 $a,b$。

### R.6 奇素数的迹约束与判别式方向

**定理。** 若 $p$ 为奇素数，则 $r=\pi(p)$ 为偶数，并且 R.5 中的整数商满足

$$
\boxed{2b-a=-p(b^2-ab-a^2).}
\tag{R10}
$$

**证明。** 因 $Q^r\equiv I\pmod p$，取行列式得
$(-1)^r\equiv1\pmod p$。奇素数下 $1\not\equiv-1$，故 $r$ 为偶数。
**证明。** 再由 R1 与 R.5 中 $a,b$ 的定义，在整数矩阵中计算

$$
1=\det Q^r
=1+p(2b-a)+p^2(b^2-ab-a^2).
$$

**证明。** 在整数环中约去非零的 $p$，即得 R10。

**定理。** 对奇素数 $p$，

$$
\boxed{\pi(p^2)=\pi(p)\iff p\mid F_{\pi(p)}/p.}
\tag{R11}
$$

**证明。** R10 模 $p$ 给出 $2b=a$。由于 $2$ 在模 $p$ 下可逆，
$p\mid a$ 当且仅当 $p\mid b$；再用 R9。

**定义。** 在模 $p$ 下令

$$
H=\begin{pmatrix}1&2\\2&-1\end{pmatrix},\qquad
\overline B=\begin{pmatrix}b&a\\a&b-a\end{pmatrix}.
$$

**定理。** 对奇素数 $p$，

$$
\boxed{2\overline B=aH,\qquad (2\overline B)^2=5a^2I.}
\tag{R12}
$$

**证明。** 由 $2b=a$ 逐项比较得到第一式；直接相乘得 $H^2=5I$，
从而得到第二式。

**命题。** 若 $p$ 为素数、$p\ne2,5$ 且 $a\not\equiv0\pmod p$，则
$\ker\overline B=0$。此外，对模 $p^2$ 的状态向量 $v$，旧周期后的差为
$pBv$；若 $v\not\equiv0\pmod p$，则该差不为零。

**证明。** 若 $\overline Bv=0$，R12 给出 $5a^2v=0$；$5a^2$ 可逆，故
$v=0$。R7 给出 $Q^rv-v=pBv$。若后者在模 $p^2$ 下为零，则
$\overline B(v\bmod p)=0$，由核为零得到 $v\equiv0\pmod p$，与假设矛盾。

### R.7 模平方上的双根障碍

**定理。** 对每个整数 $n>1$，在 $(\mathbb Z/n^2\mathbb Z)[X]$ 中有
下式；等价地，$X^2-2X+1$ 不整除 $X^n-1$：

$$
\boxed{(X-1)^2\nmid X^n-1.}
\tag{R13}
$$

**证明。** 若 $X^n-1=(X-1)^2g(X)$，形式求导并代入 $X=1$，右端为
$0$，左端为 $n$。于是 $n=0$ 于 $\mathbb Z/n^2\mathbb Z$，即
$n^2\mid n$，这与 $n>1$ 矛盾。最后的等价表述来自
$X^2-2X+1=(X-1)^2$。

### R.8 平方零系数的一阶幂律

**定义。** 对交换环 $R$，令 $R[\varphi]=R[T]/(T^2-T-1)$，并把元素写成
$z=z_a+z_b\varphi$。

**定理。** 若 $z_b^2=0$，则对每个 $k\ge0$ 有下式，其中 $k=0$ 时
第二式右端按 $0\cdot z_a^0z_b=0$ 解释：

$$
\boxed{
(z^k)_a=z_a^k,\qquad
(z^k)_b=kz_a^{k-1}z_b,
}
$$

**证明。** 对 $k$ 归纳。乘法公式为
$(xy)_a=x_ay_a+x_by_b$ 与
$(xy)_b=x_ay_b+x_by_a+x_by_b$。归纳步代入归纳假设；所有含
$z_b^2$ 的项消失，余项分别合并为 $z_a^{k+1}$ 与
$(k+1)z_a^kz_b$。

### R.9 等幂的归一化系数输运

**定理。** 设 $p>0$，$x,y\in\mathcal O$，$k,l\ge0$，且
$x_b=pA$、$y_b=pB$、$x^k=y^l$。则在 $\mathbb Z/p\mathbb Z$ 中有

$$
\boxed{
kx_a^{k-1}A=ly_a^{l-1}B.
}
\tag{R15}
$$

**证明。** 将 $x,y$ 降到 $\mathcal O/p^2\mathcal O$。因
$x_b^2=y_b^2=0$，R.8 给出等幂两侧的 $\varphi$ 系数分别为
$pkx_a^{k-1}A$ 与 $ply_a^{l-1}B$。它们模 $p^2$ 相等，所以对应整数之差
被 $p^2$ 整除；在整数整除等式中约去 $p$，再降模 $p$，即得 R15。

### R.10 带符号的 Frobenius 指标

**定义。** 对素数 $p\ne2,5$，定义

$$
\epsilon_p=\left(\frac5p\right),\qquad
n_p=p-\epsilon_p,\qquad r_p=\pi(p),
$$

$$
\eta_p=\frac{F_{r_p}}p\pmod p,\qquad
q_p=\frac{F_{n_p}}p\pmod p.
$$

**定理。** 有 $\epsilon_p\in\{1,-1\}$、$n_p>0$，并且

$$
p\mid F_{n_p},\qquad
\varphi^{n_p}=\epsilon_p\pmod p,\qquad
r_p\mid2n_p,\qquad p\nmid r_p.
$$

**证明。** 令 $\delta=2\varphi-1$，则 $\delta^2=5$。在特征 $p$ 的
二次代数中，由 Frobenius 同态与 Euler 判据，
$\delta^p=\epsilon_p\delta$。若 $\epsilon_p=1$，便有
$\varphi^{p-1}=1$；若 $\epsilon_p=-1$，则
$\varphi^p=1-\varphi=-\varphi^{-1}$，故 $\varphi^{p+1}=-1$。
两种情形统一为 $\varphi^{n_p}=\epsilon_p$。比较 $\varphi$ 系数得
$p\mid F_{n_p}$，平方后得 $\varphi^{2n_p}=1$，故 $r_p\mid2n_p$。
又 $n_p\equiv-\epsilon_p\not\equiv0\pmod p$ 且 $p$ 为奇数，所以
$p\nmid r_p$。

**命题。** 当 $p=3$ 时，$\epsilon_p=-1$、$n_p=4$、$F_{n_p}=3$，而
$\pi(3)=8$；当 $p=7$ 时，$n_p=8$、$r_p=16$。

**证明。** Legendre 符号直接给出两个 $\epsilon_p$ 的值；Fibonacci 递推给出
$F_4=3$。对 $Q$ 分别在模 $3$ 与模 $7$ 下逐次乘方，并用 R2 检查所有真因子，
得到所列最小周期。

### R.11 首次回归深度

**定义。** 对素数 $p$，令 $\nu_p$ 表示正整数的 $p$-进赋值，并定义

$$
s_p=\nu_p(C_{r_p}),\qquad r_p=\pi(p),
$$

**命题。** $C_{r_p}>0$、$p\mid C_{r_p}$，因而 $s_p$ 是有限正整数。

**证明。** $r_p>0$，故 $F_{r_p}>0$，于是 $C_{r_p}>0$。R5 对
$t=r_p$ 给出 $p\mid C_{r_p}$，所以 $s_p\ge1$ 且有限。

### R.12 周期商与 Frobenius 商的准确比例

**定理。** 对每个素数 $p\ne2,5$，

$$
\boxed{
\eta_p=-r_pq_p\quad\text{于 }\mathbb F_p,\qquad
-r_p\in\mathbb F_p^\times.
}
\tag{R14}
$$

**证明。** 在 R15 中取
$x=\varphi^{r_p}$、$y=\varphi^{n_p}$、$k=n_p$、$l=r_p$；等幂前提来自
$(\varphi^{r_p})^{n_p}=(\varphi^{n_p})^{r_p}$。由 R2 与 R.10，
$x_a=1$、$y_a=\epsilon_p$ 于模 $p$，所以

$$
n_p\eta_p=r_p\epsilon_p^{r_p-1}q_p\pmod p.
$$

**证明。** R.6 表明 $r_p$ 为偶数，故
$\epsilon_p^{r_p-1}=\epsilon_p$；又
$n_p\equiv-\epsilon_p\pmod p$。约去单位 $\epsilon_p$ 即得
$\eta_p=-r_pq_p$。R.10 已证明 $p\nmid r_p$，所以 $-r_p$ 是单位。

**命题。** 对 $p=7$，有 $n_p=8$、$r_p=16$、$q_p=3$、$\eta_p=1$，且
$-r_p\equiv5\pmod7$，从而 $\eta_p=(-r_p)q_p$。

**证明。** 递推得 $F_8=21$、$F_{16}=987$；分别先除以 $7$ 再模 $7$，
得到 $q_p=3$ 与 $\eta_p=1$，而 $-16\equiv5$ 且 $5\cdot3\equiv1$。

**定理。** 对素数 $p\ne2,5$，

$$
\boxed{\pi(p^2)=\pi(p)\iff q_p=0.}
\tag{R16}
$$

**证明。** R11 将左侧等价为 $\eta_p=0$；R14 中的系数 $-r_p$ 是单位，
故 $\eta_p=0$ 当且仅当 $q_p=0$。

### R.13 素数幂的准确缺陷深度

**定理。** 设 $p$ 为素数，$s>0$，$s+2\le ps$，$B\in\mathcal O$ 且
$p\nmid B$。则对每个 $j\ge0$，存在 $D_j\in\mathcal O$ 使下式成立，
且左侧与 $1$ 的差恰被 $p^{s+j}$ 整除而不被 $p^{s+j+1}$ 整除：

$$
\boxed{
(1+p^sB)^{p^j}=1+p^{s+j}(B+pD_j).
}
\tag{R17}
$$

**证明。** 对 $j$ 归纳。$j=0$ 时取 $D_0=0$。设第 $j$ 步括号内为
$U=B+pD_j$，则 $U\equiv B\pmod p$。对
$(1+p^{s+j}U)^p$ 作二项展开：一次项为 $p^{s+j+1}U$；中间项因
$p\mid\binom{p}{i}$ 且 $i\ge2$，都被 $p^{s+j+2}$ 整除；最高次项由
$s+2\le ps$ 也被 $p^{s+j+2}$ 整除。因此余项可吸收到新的
$D_{j+1}$ 中，且括号仍模 $p$ 等于 $B$。因为 $p\nmid B$，这个括号不被
$p$ 整除，故所述深度准确。

**定理。** 在 R17 的假设下，$1+p^sB$ 在
$(\mathcal O/p^{s+j}\mathcal O)^\times$ 中的阶恰为 $p^j$。

**证明。** R17 给出其 $p^j$ 次幂为 $1$。若 $j>0$，R17 对 $j-1$
给出的差恰只有深度 $s+j-1$，所以 $p^{j-1}$ 次幂尚不为 $1$。
该阶是 $p^j$ 的约数，却不整除 $p^{j-1}$，故只能是 $p^j$。

**命题。** 对奇素数，$s\ge1$ 即满足 $s+2\le ps$；对 $p=2$，该条件在
$s\ge2$ 时满足。

**证明。** 第一种情形有 $p\ge3$，故 $ps-(s+2)=(p-1)s-2\ge0$；
第二种情形化为 $s\ge2$。

### R.14 奇素数的完整周期塔

**定理。** 对任意奇素数 $p$ 与任意 $e\ge1$，

$$
\boxed{
\pi(p^e)=r_p\,p^{\max(e-s_p,0)},
\qquad s_p=\nu_p(C_{r_p}).
}
\tag{R18}
$$

**证明。** 由 Fibonacci 递推，
$C_{r_p}=\gcd(F_{r_p},F_{r_p-1}-1)$。结合 $s_p$ 的定义与 R2，
$\varphi^{r_p}-1$ 的两个整数坐标都被
$p^{s_p}$ 整除，但不都被 $p^{s_p+1}$ 整除。因此存在
$B\in\mathcal O$ 使

$$
\varphi^{r_p}=1+p^{s_p}B,\qquad p\nmid B.
$$

**证明。** 若 $e\le s_p$，则 $r_p$ 已在模 $p^e$ 下回归，而降模到 $p$ 又给
$r_p\mid\pi(p^e)$，故 $\pi(p^e)=r_p$。若 $e=s_p+j$，R.13 表明
$\varphi^{r_p}$ 在模 $p^e$ 下的阶为 $p^j$。令
$T=\pi(p^e)$；因 $r_p\mid T$，元素幂的阶公式给出

$$
\operatorname{ord}(\varphi^{r_p})
=\frac{T}{\gcd(T,r_p)}=\frac{T}{r_p}=p^j.
$$

**证明。** 于是 $T=r_pp^j$，与第一种情形合并即得 R18。

**定理。** 对素数 $p\ne2,5$，

$$
\boxed{q_p=0\iff s_p\ge2.}
\tag{R19}
$$

**证明。** 由 R5，$s_p\ge2$ 当且仅当
$p^2\mid C_{r_p}$，也即 $\pi(p^2)=\pi(p)$；再用 R16，即得 R19。

**命题。** 对素数 $p\ne2,5$，若 $q_p\ne0$，则

$$
\forall e\ge1,\quad \pi(p^e)=\pi(p)p^{e-1}.
$$

**证明。** 若 $q_p\ne0$，则 R19 给出 $s_p\not\ge2$，而 R.11 给出
$s_p\ge1$，故 $s_p=1$；代入 R18 即得最后一式。

### R.15 二进与分歧素数的完整周期塔

**定理。** 对每个 $e\ge1$，

$$
\boxed{
\pi(2^e)=3\cdot2^{e-1},\qquad
\pi(5^e)=20\cdot5^{e-1}.
}
\tag{R20}
$$

**证明。** 由 R2 的有限检查，
$\pi(2)=3$、$\pi(4)=6$、$\pi(5)=20$。在 $\mathcal O$ 中直接递推得到

$$
\varphi^6=1+4(1+2\varphi),
\qquad
\varphi^{20}=1+5(836+1353\varphi).
$$

**证明。** 第一式括号不被 $2$ 整除，是深度 $2$ 的原始缺陷；第二式括号不被 $5$
整除，是深度 $1$ 的原始缺陷。分别从模 $4$ 与模 $5$ 应用 R.13 的准确阶
结论，得到 $e\ge2$ 时
$\pi(2^e)=6\cdot2^{e-2}$，以及全部 $e\ge1$ 时
$\pi(5^e)=20\cdot5^{e-1}$。前者再与 $e=1$ 合并，便是 R20。

**命题。** $\pi(2^0)=\pi(5^0)=\pi(1)=1$，所以 R20 的范围不能扩为
$e=0$。

**证明。** 模 $1$ 的可逆矩阵群只有单位元，故其元素阶为 $1$；而 R20
右侧在 $e=0$ 不按自然数指数给出所需值。

### R.16 周期平台与逐层提升

**命题。** 对奇素数 $p$，若 $1\le e\le s_p$，则
$\pi(p^e)=r_p$；若 $e\ge s_p$，则

$$
\pi(p^{e+1})=p\,\pi(p^e).
$$

**证明。** 第一式由 R18 中 $\max(e-s_p,0)=0$ 得到。第二式中指数
分别为 $e-s_p+1$ 与 $e-s_p$，相差 $1$，故两周期相差因子 $p$。

### R.17 任意周期倍数的精确回归深度

**定理。** 令 $p$ 为奇素数、$r_p=\pi(p)$、
$s_p=\nu_p(C_{r_p})$。对全部 $k\ge0$ 与 $e\ge1$，

$$
\boxed{
p^e\mid C_{r_pk}\iff p^{\max(e-s_p,0)}\mid k.
}
\tag{R21}
$$

**证明。** 由 R5，左侧等价于 $\pi(p^e)\mid r_pk$。代入 R18，并在
自然数整除见证中约去正整数 $r_p$，即得右侧。$k=0$ 时两边都成立。

**定理。** 在前一定理的假设下，若 $k>0$，则

$$
\boxed{
\nu_p(C_{r_pk})=s_p+\nu_p(k).
}
\tag{R22}
$$

**证明。** 令 $d=s_p+\nu_p(k)$。由 R21，$p^d\mid C_{r_pk}$，而
$p^{d+1}\nmid C_{r_pk}$。又因 $r_pk>0$，有 $F_{r_pk}>0$，从而
$C_{r_pk}>0$；按 $p$-进赋值的定义即得 R22。
## TR. 环面返回模、有限观察与耗散结构

### TR.1 返回模与列向量约定

**定义。** 对整数二阶矩阵 $A$ 与自然数 $n$，采用列向量约定，定义返回模

$$
R(A,n)=\mathbb Z^2/(A^n-I)\mathbb Z^2,
$$

其中分母是同态 $A^n-I:\mathbb Z^2\to\mathbb Z^2$ 的像。

**定义。** 对自然数 $q$，记 $\mathbb Z/(q)=\mathbb Z/q\mathbb Z$；特别约定 $\mathbb Z/(0)=\mathbb Z$。

### TR.2 行列式为二的校准族

**定义。** 对任意自然数 $k$，定义 companion 族、balanced 族及其整数交织子

$$
C_k=\begin{pmatrix}4k+1&1\\4k&1\end{pmatrix},\qquad
D_k=\begin{pmatrix}2k+1&2\\2k(k+1)&2k+1\end{pmatrix},\qquad
P_k=\begin{pmatrix}1&0\\-2k&2\end{pmatrix}.
$$

**定理。** 对每个 $k\geq0$，有

$$
\det C_k=\det D_k=1,\qquad
\operatorname{tr}C_k=\operatorname{tr}D_k=4k+2,
$$

以及

$$
C_kP_k=P_kD_k,\qquad \det P_k=2.
$$

对每个 $n\geq0$，还有

$$
(C_k^n-I)P_k=P_k(D_k^n-I),
\qquad
\det(C_k^n-I)=\det(D_k^n-I).
$$

**证明。** 前两组等式由二阶行列式、迹和矩阵乘法直接计算。由 $C_kP_k=P_kD_k$ 对 $n$ 归纳，得 $C_k^nP_k=P_kD_k^n$，减去 $P_k$ 即得交织恒等式。两边取行列式后得到

$$
2\det(C_k^n-I)=2\det(D_k^n-I),
$$

在整数中约去 $2$ 即得最后一式。

**定理。** $P_k$ 在 $\mathbb Z^2$ 上单射，其像的指数为 $2$，因而诱导一个度数为 $2$ 的格同源；它不是整数基变换。

**证明。** 若 $P_k(p,q)=0$，则第一坐标给出 $p=0$，第二坐标再给出 $q=0$，故 $P_k$ 单射。其像恰为第二坐标为偶数的整数向量集合：正向由 $P_k(p,q)=(p,-2kp+2q)$，反向对 $(x,2y)$ 取 $(p,q)=(x,y+kx)$。因此像的指数为 $2$。整数基变换的行列式只能是 $\pm1$。

**定理。** $C_k$ 与 $D_k$ 的共同特征多项式的判别式为

$$
(4k+2)^2-4=16k(k+1).
$$

当 $k=1$ 时，其特征值生成的二次域是 $\mathbb Q(\sqrt2)$。

**证明。** 两个矩阵的行列式均为 $1$、迹均为 $4k+2$，故特征多项式为 $X^2-(4k+2)X+1$，判别式即所示。$k=1$ 时，判别式为 $32=(4\sqrt2)^2$，其平方根生成 $\mathbb Q(\sqrt2)$。

### TR.3 返回模的有限基数

**定理。** 若 $k>0$ 且 $n>0$，则

$$
\det(C_k^n-I)=2-\operatorname{tr}(C_k^n)<0,
$$

从而 $C_k^n-I$ 与 $D_k^n-I$ 都非奇异。

**证明。** $C_k$ 的所有矩阵元非负。对 $m$ 归纳可得 $C_k^m$ 的所有矩阵元非负，且两个对角元至少为 $1$。写 $n=m+1$，则

$$
\operatorname{tr}(C_k^{m+1})
=(4k+1)(C_k^m)_{00}+4k(C_k^m)_{01}
+(C_k^m)_{10}+(C_k^m)_{11}>2.
$$

又因 $\det(C_k^n)=1$，二阶恒等式 $\det(M-I)=\det M-\operatorname{tr}M+1$ 给出所述负号。TR.2 的行列式恒等式随即给出 $D_k^n-I$ 的非奇异性。

**定理。** 对任意非奇异整数二阶矩阵 $M$，商群 $\mathbb Z^2/M\mathbb Z^2$ 有限，且

$$
\#(\mathbb Z^2/M\mathbb Z^2)=|\det M|.
$$

**证明。** 对 $M$ 作整数初等行、列变换，得到 Smith 标准形 $\operatorname{diag}(d_1,d_2)$。这些变换在定义域和陪域上都是整系数可逆变换，因而不改变商群的基数。标准形的商群为 $\mathbb Z/(d_1)\times\mathbb Z/(d_2)$，其基数是 $|d_1d_2|=|\det M|$。

**定理。** 对所有 $k>0$、$n>0$，$R(C_k,n)$ 与 $R(D_k,n)$ 都是有限群，并且

$$
\#R(C_k,n)=\#R(D_k,n)=|\det(C_k^n-I)|.
$$

**证明。** 应用前一定理及 TR.2、TR.3。若 $n=0$，则 $R(A,0)=\mathbb Z^2$，故该有限性结论不适用。

### TR.4 整数交织子的偶性障碍

**定理。** 设 $k\geq0$，并设

$$
U=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in M_2(\mathbb Z).
$$

若 $C_kU=UD_k$，则

$$
c=2k((k+1)b-a),\qquad d=2(a-kb),
$$

且

$$
\det U=2\bigl(a^2-k(k+1)b^2\bigr).
$$

特别地，$\det U$ 为偶数，不存在 $\det U=\pm1$ 的整数交织子，所以 $C_k$ 与 $D_k$ 不在 $GL_2(\mathbb Z)$ 中共轭。

**证明。** 比较 $C_kU=UD_k$ 的第一行两个矩阵元，依次解得 $c$ 与 $d$。将它们代入 $ad-bc$ 并展开，得到行列式公式。可逆整数矩阵的行列式只能是 $\pm1$，与偶性矛盾。

**定理。** 在整数二阶矩阵中，全部正时间返回模的基数序列不能确定整数共轭类。

**证明。** 任取 $k>0$。TR.3 给出 $C_k$ 与 $D_k$ 在每个正时间的相同返回模基数，TR.4 则证明二者不整数共轭。

### TR.5 companion 与 balanced 族的像核恒等式

**定义。** 对 $k\geq0$ 定义群同态

$$
\pi_C:\mathbb Z^2\to\mathbb Z/(4k),qquad
\pi_C(x,y)=y\pmod{4k},
$$

以及

$$
\pi_D:\mathbb Z^2\to\mathbb Z/(2)\times\mathbb Z/(2k),qquad
\pi_D(x,y)=\bigl(x\pmod2,\ y-kx\pmod{2k}\bigr).
$$

**定理。** $\pi_C$ 满射，并且

$$
\ker\pi_C=(C_k-I)\mathbb Z^2.
$$

**证明。** 任意剩余类由 $(0,y)$ 映到，故 $\pi_C$ 满射。又

$$
(C_k-I)\binom pq=\binom{4kp+q}{4kp},
$$

所以其像包含于 $\ker\pi_C$。反之，若 $\pi_C(x,y)=0$，则 $y=4ka$；于是

$$
\binom xy=(C_k-I)\binom{a}{x-4ka}.
$$

**定理。** $\pi_D$ 满射，并且

$$
\ker\pi_D=(D_k-I)\mathbb Z^2.
$$

**证明。** 给定两个剩余类，取整数代表 $a,b$，则 $(a,b+ka)$ 映到它们。又

$$
(D_k-I)\binom pq
=\binom{2kp+2q}{2k(k+1)p+2kq},
$$

其第一坐标为偶数，且第二坐标减去第一坐标的 $k$ 倍等于 $2kp$，故像包含于核。反之，若 $(x,y)$ 位于核，写 $x=2a$、$y-kx=2kb$，则

$$
\binom xy=(D_k-I)\binom{b}{a-kb}.
$$

### TR.6 一步返回模的结构分离

**定理。** 对每个 $k\geq0$，有加法群同构

$$
R(C_k,1)\cong\mathbb Z/(4k),qquad
R(D_k,1)\cong\mathbb Z/(2)\times\mathbb Z/(2k).
$$

当 $k=0$ 时，这两式分别为 $R(C_0,1)\cong\mathbb Z$ 与 $R(D_0,1)\cong\mathbb Z/(2)\times\mathbb Z$。

**证明。** 分别对 TR.5 的满射应用第一同构定理，并以其中的像核恒等式识别分母。

**定理。** 若 $k>0$，则 $R(D_k,1)$ 的每个元素都被 $2k$ 湮灭，而 $R(C_k,1)$ 中存在不被 $2k$ 湮灭的元素。因此

$$
R(C_k,1)\not\cong R(D_k,1).
$$

**证明。** 在 $\mathbb Z/(2)\times\mathbb Z/(2k)$ 中，乘以 $2k$ 后两个分量都为零。在 $\mathbb Z/(4k)$ 中，剩余类 $1$ 不被 $2k$ 湮灭，否则 $4k$ 整除 $2k$，与 $k>0$ 矛盾。TR.6 的同构将这两个性质传回实际返回模。

**定理。** 对每个 $k>0$，$C_k$ 与 $D_k$ 的全部正时间返回模基数相同，但一步返回模的加法群不同构。

**证明。** 第一部分由 TR.3，第二部分由前一定理。

### TR.7 返回模结构与标量观察

**命题。** 在校准族 $C_k,D_k$ 中，标量序列

$$
n\longmapsto\#R(A,n),\qquad n>0,
$$

不决定一步返回模的群结构，而一步返回模的湮灭阶能够区分 $C_k$ 与 $D_k$。

**证明。** TR.6 同时给出相同标量序列和不同的 $2k$-湮灭性质。

### TR.8 交织子范数与模共轭判据

**定理。** 设 $S$ 为交换环，$k\geq0$。矩阵 $U\in M_2(S)$ 满足 $C_kU=UD_k$ 当且仅当存在 $a,b\in S$ 使

$$
U=U(a,b)=
\begin{pmatrix}
a&b\\
2k((k+1)b-a)&2(a-kb)
\end{pmatrix}.
$$

此时

$$
\det U(a,b)=2\bigl(a^2-k(k+1)b^2\bigr).
$$

**证明。** 正向由交织等式第一行的两个分量依次求出第二行；整个推导没有除法。反向把所示矩阵代入四个矩阵元，四式均成立。行列式公式由展开得到。

**定义。** 对自然数 $m$，称 $C_k$ 与 $D_k$ 在 $\mathbb Z/(m)$ 上共轭，如果存在 $P,Q\in M_2(\mathbb Z/(m))$ 满足

$$
PQ=QP=I,qquad C_kP=PD_k.
$$

**定理。** 对所有自然数 $k,m$，

$$
C_k\text{ 与 }D_k\text{ 在 }\mathbb Z/(m)\text{ 上共轭}
\quad\Longleftrightarrow\quad m\text{ 为奇数}.
$$

**证明。** 若 $m=2r+1$，在 $\mathbb Z/(m)$ 中令 $u=-r$，则 $2u=1$。取

$$
P=\begin{pmatrix}1&0\\-2k&2\end{pmatrix},qquad
Q=\begin{pmatrix}1&0\\k&u\end{pmatrix}.
$$

直接乘法给出 $PQ=QP=I$ 与 $C_kP=PD_k$。反之，若 $m$ 为正偶数，则存在环同态 $\mathbb Z/(m)\to\mathbb Z/(2)$。任何可逆交织子都满足 $\det(P)\det(Q)=1$；TR.8 的行列式公式在 $\mathbb Z/(2)$ 中却使左边为 $0$，矛盾。若 $m=0$，系数环为 $\mathbb Z$，TR.4 排除可逆交织子。$m=1$ 为零环，且属于奇数情形。

### TR.9 环面作用与周期群

**定义。** 令 $V=\mathbb R^2$，令 $j:\mathbb Z^2\to V$ 为逐坐标嵌入，$L=j(\mathbb Z^2)$，并令

$$
\mathbb T^2=V/L.
$$

对整数矩阵 $A$，其实线性延拓保持 $L$，故诱导连续群同态

$$
f_A:\mathbb T^2\to\mathbb T^2,qquad [x]\longmapsto[Ax].
$$

**定义。** 对自然数 $n$，定义周期整除 $n$ 的固定点群

$$
K(A,n)=\ker f_{A^n-I}.
$$

**定理。** 对整数矩阵 $A,B$ 与自然数 $n$，

$$
f_A\circ f_B=f_{AB},qquad f_A^n=f_{A^n},qquad
z\in K(A,n)\Longleftrightarrow f_A^n(z)=z.
$$

**证明。** 每个等式在代表元上分别化为 $A(Bx)=(AB)x$、矩阵幂的归纳以及 $(A^n-I)x=A^nx-x$。由于整数矩阵保持格 $L$，这些代表元计算均良定义。

### TR.10 环面固定点与返回商

**定理。** 设 $M=A^n-I$ 且 $\det M\ne0$。则存在加法群同构

$$
R(A,n)\cong K(A,n).
$$

其逆可写为

$$
[x]\longmapsto[Mx]
\quad\text{从}\quad
M_{\mathbb R}^{-1}\mathbb Z^2/\mathbb Z^2
\quad\text{到}\quad
\mathbb Z^2/M\mathbb Z^2.
$$

**证明。** 由 $\det M\ne0$，实线性映射 $M_{\mathbb R}$ 可逆。定义

$$
b_M:\mathbb Z^2\to\ker f_M,qquad
z\longmapsto[M_{\mathbb R}^{-1}j(z)].
$$

若 $[x]\in\ker f_M$，则 $M_{\mathbb R}x\in L$，故存在 $z\in\mathbb Z^2$ 使 $M_{\mathbb R}x=j(z)$，从而 $b_M(z)=[x]$；所以 $b_M$ 满射。另一方面，$b_M(z)=0$ 当且仅当存在 $w\in\mathbb Z^2$ 使 $M_{\mathbb R}^{-1}j(z)=j(w)$，也即 $z=Mw$。因此 $\ker b_M=M\mathbb Z^2$，第一同构定理给出结论。所写逆映射由同一计算得出。

**定理。** 对 $k>0$、$n>0$，$f_{C_k}$ 与 $f_{D_k}$ 的周期整除 $n$ 的固定点群具有相同有限基数；在 $n=1$ 时，这两个固定点群不同构。

**证明。** TR.3 保证相关行列式非零，TR.10 把固定点群分别同构到返回模，再应用 TR.3 与 TR.6。

### TR.11 粒子流与环面自同构的同痕障碍

**假设。** 设 $T\geq0$，$\Phi:[0,T]\times\mathbb T^2\to\mathbb T^2$ 连续，且 $\Phi_0=\operatorname{id}_{\mathbb T^2}$；对每个 $t$，记 $\Phi_t(x)=\Phi(t,x)$。

**定理。** $\Phi_T$ 与恒等映射同痕，因而 $\Phi_T$ 在一阶同调群上的诱导映射是恒等。若整数环面自同构 $f_A$ 在一阶同调上的作用为非恒等矩阵 $A$，则 $\Phi_T\ne f_A$。

**证明。** 映射 $(s,x)\mapsto\Phi_{sT}(x)$ 是从恒等映射到 $\Phi_T$ 的同痕。同调的同痕不变性给出第一项。若 $\Phi_T=f_A$，则二者在一阶同调上的作用相同，迫使 $A=I$，矛盾。

**定义。** 对常系数对称逆度量

$$
H=\begin{pmatrix}h_{00}&h_{01}\\h_{01}&h_{11}\end{pmatrix}
$$

和黏性 $\nu$，定义平坦二维零压力、零外力的 Navier--Stokes 残差

$$
\mathcal R_H(v)=\partial_tv+(v\cdot\nabla)v
-\nu\bigl(h_{00}\partial_{xx}+2h_{01}\partial_{xy}+h_{11}\partial_{yy}\bigr)v.
$$

### TR.12 格同源下的剪切解与度量输运

**定义。** 在两个空间坐标均以 $2\pi$ 为周期的平坦环面上，令

$$
u(t,X,Y)=(e^{-\nu t}\cos Y,0),qquad
Q_k=P_k^{-1}=\begin{pmatrix}1&0\\k&1/2\end{pmatrix},
$$

并定义

$$
v(t,x,y)=Q_ku(t,P_k(x,y))
=(1,k)e^{-\nu t}\cos(-2kx+2y).
$$

**定理。** $u$ 光滑、无散度，且满足欧氏度量下的无外力、零压力 Navier--Stokes 方程

$$
\partial_tu+(u\cdot\nabla)u-\nu\Delta u=0.
$$

**证明。** 直接求导得 $\operatorname{div}u=0$、$(u\cdot\nabla)u=0$、$\partial_tu=\nu\Delta u$。

**定理。** 令

$$
G_k=P_k^{\mathsf T}P_k,qquad
H_k=Q_kQ_k^{\mathsf T}
=\begin{pmatrix}1&k\\k&k^2+1/4\end{pmatrix}.
$$

则 $G_kH_k=H_kG_k=I$，且 $H_k$ 正定。具体地，对 $(r,s)\ne(0,0)$，

$$
(r,s)H_k(r,s)^{\mathsf T}=(r+ks)^2+s^2/4>0.
$$

**证明。** 由 $P_kQ_k=Q_kP_k=I$ 直接得到两侧逆关系。二次型恒等式由展开得到；若 $s\ne0$，第二项为正，若 $s=0$，则 $r\ne0$ 且第一项为正。

**定义。** 对实数 $\lambda$，令

$$
v_\lambda(t,x,y)=(1,k)e^{-\nu\lambda t}\cos(-2kx+2y).
$$

**定理。** $v_\lambda$ 关于时空变量光滑，并在两个空间方向上均为 $2\pi$ 周期；它无散度，且

$$
\mathcal R_H(v_\lambda)
=\nu\bigl(4h_{00}k^2-8h_{01}k+4h_{11}-\lambda\bigr)v_\lambda.
$$

**证明。** 光滑性与周期性由指数函数、余弦函数及整数频率直接得到。令 $\ell=(-2k,2)$、$a=(1,k)$，则 $\ell\cdot a=0$，所以散度及完整对流项消失。再用

$$
\partial_tv_\lambda=-\nu\lambda v_\lambda,\qquad
\partial_{xx}v_\lambda=-4k^2v_\lambda,\qquad
\partial_{xy}v_\lambda=4kv_\lambda,\qquad
\partial_{yy}v_\lambda=-4v_\lambda
$$

代入 TR.11 的残差定义，即得公式。

**定理。** $v_1=v$ 满足逆度量 $H_k$ 下的方程；在欧氏逆度量下则有

$$
\mathcal R_I(v)=\nu(4k^2+3)v.
$$

若 $\nu>0$，该残差在 $(t,x,y)=(0,0,0)$ 的第一分量严格为正。另一方面，

$$
w(t,x,y)=(1,k)e^{-4\nu(k^2+1)t}\cos(-2kx+2y)
$$

满足欧氏度量下的无外力方程，并且 $w(0,x,y)=v(0,x,y)$。

**证明。** 在残差公式中依次代入 $(h_{00},h_{01},h_{11},\lambda)=(1,k,k^2+1/4,1)$、$(1,0,1,1)$ 与 $(1,0,1,4(k^2+1))$。第一组和第三组的系数为零，第二组的系数为 $4k^2+3$。初值等式由令 $t=0$ 得到。

**定理。** $H_k$ 的最小特征值没有与 $k$ 无关的正下界，并且

$$
\lambda_{\min}(H_k)\leq\frac{1}{4(k^2+1)}\longrightarrow0.
$$

**证明。** 在 Rayleigh 商中取非零向量 $(-k,1)$。TR.12 的二次型等于 $1/4$，而该向量的欧氏长度平方为 $k^2+1$。

### TR.13 Hilbert 空间的耗散管与二次李雅普诺夫证书

**假设。** 设 $H$ 为实内积空间，$u:[0,T]\to H$ 连续，并在 $[0,T)$ 具有右导数 $\dot u$。设 $\gamma>0$、$\rho\geq0$，且

$$
\langle u(t),\dot u(t)\rangle
\leq-\gamma\|u(t)\|^2+\rho\|u(t)\|.
$$

**定理。** 对每个 $t\in[0,T]$，

$$
\|u(t)\|\leq e^{-\gamma t}\|u(0)\|
+\frac{\rho}{\gamma}\bigl(1-e^{-\gamma t}\bigr).
$$

特别地，当 $\rho=0$ 时，$\|u(t)\|\leq e^{-\gamma t}\|u(0)\|$。

**证明。** 对 $\delta>0$ 定义

$$
z_\delta(t)=\sqrt{\|u(t)\|^2+\delta^2}.
$$

被开方数严格为正，故在 $u(t)=0$ 时链式法则仍适用。记 $n=\|u(t)\|$、$z=z_\delta(t)$，则 $z\geq n$、$z\geq\delta$，并且

$$
z_\delta'(t)=\frac{\langle u(t),\dot u(t)\rangle}{z_\delta(t)}
\leq-\gamma z_\delta(t)+\rho+\gamma\delta.
$$

最后一个不等式可在乘以正数 $z$ 后由恒等式

$$
(-\gamma z+\rho+\gamma\delta)z-(-\gamma n^2+\rho n)
=\rho(z-n)+\gamma\delta(z-\delta)
$$

得到。标量 Gronwall 比较给出

$$
z_\delta(t)\leq e^{-\gamma t}z_\delta(0)
+\frac{\rho+\gamma\delta}{\gamma}\bigl(1-e^{-\gamma t}\bigr).
$$

由 $\|u(t)\|\leq z_\delta(t)$，再令 $\delta\downarrow0$，利用平方根与指数函数的连续性即得结论。

**定理。** 设 $\gamma>0$、$\rho\geq0$，$u:[0,T]\to H$ 连续且在 $[0,T)$ 具有右导数。设 $A(t):H\to H$ 为有界线性算子，$f:[0,T]\to H$ 连续，并且

$$
u'(t)=A(t)u(t)+f(t),\qquad
\langle x,A(t)x\rangle\leq-\gamma\|x\|^2,qquad
\|f(t)\|\leq\rho.
$$

则 $u$ 满足前一定理的同一指数管估计。

**证明。** 由 Cauchy--Schwarz 不等式，

$$
\langle u,u'\rangle
=\langle u,A(t)u\rangle+\langle u,f\rangle
\leq-\gamma\|u\|^2+\rho\|u\|.
$$

应用前一定理。

**定义。** 设 $L:H\to H$ 线性，$B:H\times H\to H$ 双线性，$f\in H$，定义

$$
F(x)=Lx-B(x,x)+f.
$$

**假设。** 对所有 $a,b,w\in H$，设

$$
\langle b,B(a,b)\rangle=0,qquad
\langle w,Lw\rangle\leq-\mu\|w\|^2,qquad
-\langle w,B(w,v)\rangle\leq G\|w\|^2,
$$

并设 $G<\mu$、$F(v)=0$。

**定理。** 对所有 $w,x\in H$，

$$
\langle w,F(v+w)-F(v)\rangle
=\langle w,Lw\rangle-\langle w,B(w,v)\rangle,
$$

以及

$$
\langle x-v,F(x)-F(v)\rangle
\leq-(\mu-G)\|x-v\|^2.
$$

**证明。** 展开 $B(v+w,v+w)$。由假设，$\langle w,B(v,w)\rangle=0$ 与 $\langle w,B(w,w)\rangle=0$，只留下 $B(w,v)$。再代入关于 $L$ 与 $B(w,v)$ 的两个二次型上界。

**定理。** 在上述假设下，对每个 $x\in H$，

$$
\|x-v\|\leq\frac{\|F(x)\|}{\mu-G}.
$$

并且 $v$ 是 $F$ 的唯一零点。

**证明。** 若 $x=v$，结论显然。否则将前一定理与 $F(v)=0$ 合并，取相反数后用 Cauchy--Schwarz 不等式，得到

$$
(\mu-G)\|x-v\|^2
\leq\|x-v\|\,\|F(x)\|.
$$

约去正数 $\|x-v\|$ 即得距离界。若再有 $F(x)=0$，右边为零，故 $x=v$。

**定理。** 设 $\rho\geq0$，且 $u:[0,T]\to H$ 连续并在 $[0,T)$ 具有右导数。若轨迹满足

$$
u'(t)=F(u(t))+r(t),\qquad \|r(t)\|\leq\rho,
$$

则对 $t\in[0,T]$，

$$
\|u(t)-v\|\leq e^{-(\mu-G)t}\|u(0)-v\|
+\frac{\rho}{\mu-G}\bigl(1-e^{-(\mu-G)t}\bigr).
$$

**证明。** 令 $e=u-v$。前述负裕量和 Cauchy--Schwarz 不等式给出

$$
\langle e,e'\rangle
\leq-(\mu-G)\|e\|^2+\rho\|e\|.
$$

应用 TR.13 的耗散管定理。

### TR.14 受迫剪切不动点与耗散记忆

**定义。** 对 $k\geq0$、$\nu>0$，令

$$
\Phi_k(x,y)=(1,k)\cos(-2kx+2y),qquad
\Gamma_k=4\nu(k^2+1),qquad
u_a(t,x,y)=a(t)\Phi_k(x,y).
$$

**定理。** 若 $a$ 可微，则 $u_a$ 无散度，且欧氏零压力残差满足

$$
\partial_tu_a+(u_a\cdot\nabla)u_a-\nu\Delta u_a
=(a'+\Gamma_ka)\Phi_k.
$$

此外，$a(t)=u_a(t,0,0)_1$，其中下标 $1$ 表示第一坐标分量。

**证明。** 波矢 $(-2k,2)$ 与幅向量 $(1,k)$ 正交，故散度和对流项消失。坐标二阶导数之和为 $-4(k^2+1)u_a$，从而得到残差公式。在 $(x,y)=(0,0)$ 处，第一坐标分量的幅值为 $1$，故得到读数恒等式。

**定理。** 对常数 $c$，时间不变场

$$
u_*(x,y)=c\Phi_k(x,y)
$$

是外力 $f_*=\Gamma_kc\Phi_k$ 下的稳态解。若 $\rho\geq0$ 且

$$
a'=-\Gamma_k(a-c)+r,qquad |r(t)|\leq\rho,
$$

则对所有 $t\in[0,T]$、$(x,y)$ 及两个坐标分量 $i$，

$$
|u_{a,i}(t,x,y)-u_{*,i}(x,y)|
\leq(1+k)\left[
e^{-\Gamma_kt}|a(0)-c|
+\frac{\rho}{\Gamma_k}(1-e^{-\Gamma_kt})
\right].
$$

**证明。** 取 $a\equiv c$ 代入前一定理即得稳态方程。对 $a-c$ 应用 TR.13 的标量情形，再用

$$
|\Phi_{k,i}(x,y)|\leq1+k
$$

即可得到一致空间界。

**定义。** 对实常数 $a,b,d$，考虑二状态系统

$$
x'=-ax+by,qquad y'=-bx-dy,
$$

并定义能量 $E=x^2+y^2$。

**定理。** 该系统满足精确能量恒等式

$$
E'=-2ax^2-2dy^2.
$$

若 $a,d\geq\gamma>0$，则对 $t\in[0,T]$，

$$
E(t)\leq E(0)e^{-2\gamma t},
$$

且该估计与耦合常数 $b$ 无关。

**证明。** 对 $x^2+y^2$ 求导，两个交叉项 $2bxy$ 与 $-2bxy$ 相消。于是 $E'\leq-2\gamma E$，标量 Gronwall 比较给出结论。

**定理。** 若 $b\ne0$，则隐藏状态由可见状态及其导数精确恢复：

$$
y=\frac{x'+ax}{b}.
$$

若观测值满足 $|\widehat x-x|\leq\varepsilon_x$ 与 $|\widehat v-x'|\leq\varepsilon_v$，则

$$
\left|\frac{\widehat v+a\widehat x}{b}-y\right|
\leq\frac{\varepsilon_v+|a|\varepsilon_x}{|b|}.
$$

**证明。** 第一式由 $x'=-ax+by$ 解出 $y$。第二式将重建误差写成

$$
\frac{(\widehat v-x')+a(\widehat x-x)}{b}
$$

并应用三角不等式。

**定理。** 若 $t\geq0$，$x$ 在 $[0,t]$ 上连续且 $y$ 在该区间满足隐藏方程，则

$$
y(t)=e^{-dt}\left(y(0)-b\int_0^t e^{ds}x(s)\,ds\right).
$$

因此可见变量满足精确 Volterra 方程

$$
x'(t)=-ax(t)+be^{-dt}y(0)
+\int_0^tK(t-s)x(s)\,ds,
\qquad
K(\tau)=-b^2e^{-d\tau}.
$$

**证明。** 对 $e^{dt}y(t)$ 求导，得

$$
\frac{d}{dt}\bigl(e^{dt}y(t)\bigr)=-be^{dt}x(t).
$$

在 $[0,t]$ 上积分并乘以 $e^{-dt}$ 得隐藏历史公式。将其代入 $x'=-ax+by$，再用

$$
e^{-dt}e^{ds}=e^{-d(t-s)}
$$

即得卷积形式及核 $K$。

**定理。** 对相同可见输入 $x$，若 $y,z$ 是两个隐藏解且 $d>0$，则

$$
|b(y(t)-z(t))|
\leq |b|e^{-dt}|y(0)-z(0)|.
$$

**证明。** 差 $q=y-z$ 满足 $q'=-dq$，故 $q(t)=e^{-dt}q(0)$；取绝对值并乘以 $|b|$。

**定理。** 若 $d\ne0$ 且隐藏方程处于稳态，即 $-bx-dy=0$，则

$$
y=-\frac{b}{d}x,qquad
-ax+by=-\left(a+\frac{b^2}{d}\right)x.
$$

**证明。** 第一式由稳态方程除以 $d$ 得到；代入可见方程右端并整理即得第二式。
### TR.15 (a,−1)-Fibonacci 不动点与 Benfield–Lippard 猜想 6.5(v) 的反例

#### 定义 15.1 序列、Pisano 周期与不动点

对整数 $a$，定义 $(a,-1)$-Fibonacci 序列

$$
U_0=0,\qquad U_1=1,\qquad U_{n+2}=aU_{n+1}-U_n\quad(n\geq0).
$$

对整数 $m>1$，其 Pisano 周期 $\pi_{(a,-1)}(m)$ 是满足
$(U_T,U_{T+1})\equiv(0,1)\pmod m$ 的最小正整数 $T$；若
$\pi_{(a,-1)}(m)=m$，则称 $m$ 为不动点。
递推在相邻两项上的变换可逆，因此模 $m$ 的序列从初始项起即为周期序列。
令

$$
A_a=\begin{pmatrix}a&-1\\1&0\end{pmatrix}.
$$

由于 $\det A_a=1$，它模 $m$ 属于有限群 $\mathrm{SL}_2(\mathbb Z/m\mathbb Z)$。
递推归纳给出，对 $n\geq1$，

$$
A_a^n=\begin{pmatrix}U_{n+1}&-U_n\\U_n&-U_{n-1}\end{pmatrix}.
$$

当 $(U_n,U_{n+1})\equiv(0,1)$ 时，递推还给出 $U_{n-1}\equiv-1$，
故该返回条件等价于 $A_a^n\equiv I\pmod m$。
因此 $\pi_{(a,-1)}(m)$ 也就是 $A_a$ 模 $m$ 的乘法阶。

#### 引文 15.2 猜想的正参数第五分支与临界素数

Benfield–Lippard，*Fixed points of K-Fibonacci sequences*，
arXiv:2404.08194v2，§6「Final Thoughts」的猜想 6.5
（文献条目 [benfieldlippard2024fixedpoints](../../../Library/ArithUnits/benfieldlippard2024fixedpoints.md)）
先令 $p_1^{e_1}\cdots p_t^{e_t}$ 为 $a^2+4b$ 的素因数分解，取 $b=-1$、$a>2$。
对每个 $m>1$ 及非负整数 $j_1,\ldots,j_t$，猜想以五个分支刻画
$\pi_{(a,-1)}(m)=m$ 的充要条件。其中第 (v) 项原文为：

> (v) $a \equiv -1 \pmod{6}$ and $m = p_i^{j_i}$ or $m = 6 \cdot p_1^{j_1+1} \cdots p_t^{j_t}$.

这里 $p_i$ 均取自 $a^2-4$ 的素因数；第二种形式中的 $j_1+1$ 保留原文。
因此这一分支的必要方向声称：当 $a>2$ 且 $a\equiv-1\pmod6$ 时，
任何不动点 $m>1$ 都是一个素数幂，或是 $6$ 的倍数。

紧接猜想的文字为：

> It appears that in the previous conjecture, only one prime has powers that are fixed points for any given $a$; let this be the *critical prime* for the $(a,-1)$-Fibonacci sequence.

作者继而指出这个素数不总是 $a^2-4$ 的最小或最大素因数，并说 $a=3$ 是没有临界素数的特殊情形。
这一段是猜想之后的观察，不是已经证明的唯一性定理。

#### 命题 15.3 混合模数十五的反例及其参数族

对 $a=47$，有

$$
\pi_{(47,-1)}(15)=15,\qquad
47\equiv-1\pmod6,\qquad 47^2-4=2205=3^2\cdot5\cdot7^2.
$$

不动点 $15$ 不属于引文 15.2 第 (v) 项列出的任何一种形式，
所以该项的「仅当」方向为假。
更一般地，每个满足 $a>2$ 且 $a\equiv47\pmod{30}$ 的整数 $a$
都有 $\pi_{(a,-1)}(15)=15$，并给出同一分支的反例。

证明。若 $a\equiv2\pmod r$，递推与初值归纳给出 $U_n\equiv n\pmod r$。
对 $a=47$，模 $3$ 与模 $5$ 的剩余序列分别为

$$
\begin{aligned}
(U_n\bmod3)_{n\geq0}&=0,1,2,0,1,2,\ldots,\\
(U_n\bmod5)_{n\geq0}&=0,1,2,3,4,0,1,2,3,4,\ldots.
\end{aligned}
$$

返回初始相邻对 $(0,1)$ 的正时刻分别恰为 $3$ 和 $5$ 的正倍数。
由中国剩余定理，模 $15$ 返回等价于同时模 $3$、模 $5$ 返回，故

$$
\pi_{(47,-1)}(15)
=\operatorname{lcm}\bigl(\pi_{(47,-1)}(3),\pi_{(47,-1)}(5)\bigr)
=\operatorname{lcm}(3,5)=15.
$$

$15=3\cdot5$ 有两个不同素因数，不是任何单一素数的幂，且 $6\nmid15$；
这同时排除了第 (v) 项的两种形式。
若 $a\equiv47\pmod{30}$，则仍有 $a\equiv2\pmod{15}$ 及
$a\equiv-1\pmod6$，相同的剩余序列与排除论证逐字适用。证毕。

#### 命题 15.4 两个完整的素数幂不动点塔

对每个整数 $e\geq1$，

$$
\pi_{(47,-1)}(3^e)=3^e,\qquad
\pi_{(47,-1)}(5^e)=5^e.
$$

因此，同一参数 $a=47$ 下，两个不同素数 $3,5$ 的全部正整数次幂都是不动点；
引文 15.2 的临界素数唯一性观察即使按完整幂塔理解也不成立。

证明。写 $A=A_{47}$。直接整数矩阵乘法给出

$$
\begin{aligned}
A^3&=I+3B_3,&
B_3&=\begin{pmatrix}34576&-736\\736&-16\end{pmatrix},\\
A^5&=I+5B_5,&
B_5&=\begin{pmatrix}45785971&-974611\\974611&-20746\end{pmatrix}.
\end{aligned}
$$

两个种子的左上角分别满足 $34576\equiv1\pmod3$ 与
$45785971\equiv1\pmod5$，所以 $B_p$ 至少有一个元素不被 $p$ 整除。
命题 15.3 的剩余序列还给出 $A$ 模 $p$ 的阶恰为 $p$，其中 $p=3,5$。

以下提升论证适用于任意奇素数 $p$ 以及满足
$A^p=I+pB$、$B\not\equiv0\pmod p$ 的整数矩阵 $A,B$。
对每个整数 $r\geq1$，归纳构造整数矩阵 $D_r$，使得

$$
A^{p^r}=I+p^rD_r,\qquad D_r\equiv B\pmod p.
$$

$r=1$ 时取 $D_1=B$。若结论对 $r$ 成立，因 $I$ 与 $D_r$ 交换，
普通二项式展开在它们生成的交换子环中给出

$$
A^{p^{r+1}}
=(I+p^rD_r)^p
=I+p^{r+1}D_r+\sum_{k=2}^{p}\binom pk p^{rk}D_r^k.
$$

当 $2\leq k\leq p-1$ 时，$p\mid\binom pk$ 且
$rk+1\geq r+2$；当 $k=p$ 时，$rp\geq r+2$，这里使用 $p\geq3$。
所以末项之和逐元素被 $p^{r+2}$ 整除，能够写成
$p^{r+2}E_r$。取 $D_{r+1}=D_r+pE_r$ 即得归纳步。
等价地，对每个 $j\geq0$ 存在整数矩阵 $C_j$ 使

$$
A^{p^{j+1}}=I+p^{j+1}(B+pC_j).
$$

于是 $A^{p^e}\equiv I\pmod{p^e}$，其阶整除 $p^e$。
当 $e\geq2$ 时，$D_{e-1}\equiv B\not\equiv0\pmod p$，故
$A^{p^{e-1}}-I=p^{e-1}D_{e-1}$ 不被 $p^e$ 逐元素整除。
阶既整除 $p^e$ 又不整除 $p^{e-1}$，只能等于 $p^e$。
$e=1$ 的阶已由剩余序列确定；分别代入两个种子即得全部结论。证毕。

#### 注记 15.5 黄金坐标与 Wall–Sun–Sun 边界

若 $\varphi^2=\varphi+1$，则 $\varphi^8=13+21\varphi$，其迹为
$L_8=2\cdot13+21=47$；相应基矩阵
$\left(\begin{smallmatrix}21&0\\13&-1\end{smallmatrix}\right)$ 的行列式为
$-21=-F_8$，故只有在 $21$ 模 $m$ 可逆时它才是可逆基变换。

经典 Wall–Sun–Sun 问题针对普通 Fibonacci 递推
$F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$，询问是否存在素数 $p\ne2,5$ 使
$p^2\mid F_{p-(5/p)}$，其中 $(5/p)$ 为 Legendre 符号。
命题 15.3 与 15.4 针对 $(47,-1)$ 递推，并未判定这一经典存在性问题。

## 追加锚（本行以下为增补区）

## Appendix U. Fibonacci square classes, valuation parity, and prime-square obstructions

### U.1. Definitions and classical arithmetic inputs

Let F_0=0, F_1=1 and F_(n+2)=F_(n+1)+F_n. Let phi be the original golden unit with phi^2=phi+1, and L_n=trace(phi^n). For a positive integer M, define

\[
\operatorname{core}(M)=\prod_{r\ \mathrm{prime},\ v_r(M)\ \mathrm{odd}}r,
\qquad s(n)=\operatorname{core}(F_n)\quad(n\ge1).
\]

The core is the unique positive squarefree d such that M=d*u^2 for a positive integer u. It is distinct from the radical, which retains every prime divisor. Write omega(M) for the number of distinct prime divisors, and Omega(M) for their number counted with multiplicity.

**Classical square-class theorem.** For positive indices, the only nonsingleton square classes of Fibonacci numbers have index sets `{1,2,12}` and `{3,6}`. Thus `s(m)=s(n)` at distinct indices only in one of those two sets. In particular F_n is a square only at n=1,2,12, and distinct positive odd indices always have different cores.

This is the square-class classification in P. Ribenboim, *Square classes of Fibonacci and Lucas numbers*, Portugaliae Mathematica 46(2) (1989), 159-175. An explicit statement by the same author is *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), 3-14, section 3.4, printed page 8: https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf . The classification is an external classical theorem throughout this appendix.

**Classical valuation theorem.** If r is an odd prime, d,k are positive integers, and r divides F_d, then

\[
v_r(F_{dk})=v_r(F_d)+v_r(k).\tag{U.1}
\]

Also `v_5(F_t)=v_5(t)`. For r=2,

\[
v_2(F_t)=
\begin{cases}
0,&3\nmid t,\\
1,&t\equiv3\pmod6,\\
v_2(t)+2,&6\mid t.
\end{cases}\tag{U.2}
\]

These are Lengyel's formulas as recorded in L. A. Medina and E. Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271, Theorem 1.4, https://arxiv.org/abs/0910.2907 . Formula U.1 follows by applying the rank-based formula twice and subtracting the same initial valuation. It does not require that initial valuation to be one. The rank alpha(r) is the least positive d with r dividing F_d; the same source, Theorem 1.2, gives

\[
\alpha(r)\mid r-\left(\frac5r\right),\qquad r\ne2,5.
\tag{U.3}
\]

### U.2. Support transport under odd square multipliers

**Theorem.** For every m>=1 and every odd t>1,

\[
\boxed{s(m)\mid s(mt^2),\qquad s(m)\ne s(mt^2).}\tag{U.4}
\]

**Proof.** If an odd prime r has odd valuation in F_m, then U.1 changes that valuation by `v_r(t^2)=2v_r(t)`, so r still occurs in the core. For r=2, oddness of t preserves whether m is even and preserves v_2(m). If 3 divides m, U.2 therefore gives the same v_2 for F_m and F_(mt^2). If 3 does not divide m, the prime 2 is absent from s(m), which is sufficient for core divisibility. Thus every prime of s(m) remains in s(mt^2).

Equality would put the distinct indices m and mt^2 in one exceptional square class. The ratios of distinct larger to smaller indices in those classes are 2,6,12, and none is an odd square greater than one. Equality is impossible.

**Corollary.** For fixed m>=1, fixed odd t>1 and j>=0,

\[
\omega(s(mt^{2j}))\ge\omega(s(m))+j.\tag{U.5}
\]

**Proof.** Every step in U.4 is strict divisibility between squarefree integers, hence adds at least one prime divisor. Induction on j proves the bound.

### U.3. A lower bound for odd indices

**Lemma.** Suppose q is an odd prime other than five, and d is a positive integer every prime divisor of which is at least q. Then q does not divide F_d.

**Proof.** Otherwise alpha(q)>1 would divide d and also q-1 or q+1 by U.3. Every prime divisor of either even integer q-1 or q+1 is less than q. Taking a prime divisor of alpha(q) contradicts the hypothesis on d. The case d=1 is also immediate from F_1=1.

**Theorem.** For every positive odd integer m,

\[
\boxed{
\omega(s(m))\ge\Omega(m)-\left\lfloor\frac{v_5(m)}2\right\rfloor.
}\tag{U.6}
\]

**Proof.** Construct an increasing chain of odd divisors from 1 to m as follows. First multiply by all prime factors q>=7, in nonincreasing order and with multiplicity. Write `v_5(m)=2b+delta`, with delta either zero or one. Next multiply once by five if delta=1, then multiply by 25 exactly b times. Finally multiply by three `v_3(m)` times.

At a q>=7 step, or at a q=3 step, the lemma shows q does not divide the current Fibonacci number. Thus the multiplier q contributes no change to the valuation of any old odd prime divisor. Equation U.2 shows that any old factor two also retains its odd valuation, since all indices and multipliers are odd. The existing core therefore divides the next one. At the possible first five step, the current index is coprime to five, so U.1 and `v_5(F_d)=v_5(d)=0` give the same inclusion. At each 25 step the valuation at five changes by two and all other old valuations remain unchanged. Again the old core divides the new one.

All indices in the chain are odd and distinct. The square-class theorem makes every inclusion strict, so every step adds at least one prime divisor. The number of steps is

\[
\sum_{q\ne5}v_q(m)+b+\delta
=\Omega(m)-\left\lfloor v_5(m)/2\right\rfloor.
\]

The chain starts at s(1)=1, whose support is empty. Counting its strict inclusions proves U.6.

**Corollary.** For every positive odd n,

\[
\boxed{\omega(\operatorname{core}(F_{n^2}))\ge2\Omega(n)-v_5(n).}\tag{U.7}
\]

**Proof.** Apply U.6 to m=n^2, using `Omega(n^2)=2Omega(n)` and `v_5(n^2)=2v_5(n)`.

### U.4. Complete prime-value classification for A250093

The sequence OEIS A250093 is

\[
a(n)=\operatorname{core}(F_{n^2}),\qquad n\ge1.
\]

The externally stated conjecture asserts that its only prime values are 3 and 3001. The following gives the exact indices as well.

**Theorem.** For every n>=1,

\[
\boxed{\operatorname{Prime}(a(n))\ \Longleftrightarrow\ n=2\ \lor\ n=5.}\tag{U.8}
\]

**Proof for even n.** Since 4 divides n^2 and F_4=3, U.1 gives

\[
v_3(F_{n^2})=1+v_3(n^2/4)=1+2v_3(n),
\]

which is odd. Hence 3 divides a(n). If a(n) is prime, it equals 3=s(4). The square-class theorem forces n^2=4, because the square class of F_4 is a singleton. Thus n=2.

**Proof for odd n.** The case n=1 gives a(1)=1. For n>1, if a(n) is prime, U.7 gives

\[
1\ge 2\Omega(n)-v_5(n)
=v_5(n)+2\sum_{q\ne5}v_q(n).
\]

Every term on the right is nonnegative. Therefore no prime other than five divides n, and `v_5(n)<=1`. As n>1, necessarily n=5.

Conversely,

\[
F_4=3,\qquad F_{25}=75025=5^2\cdot3001.
\]

The number 3001 is prime: trial division by the primes through sqrt(3001)<55, namely 2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53, gives no divisor. Hence a(2)=3 and a(5)=3001 are prime. This completes both directions of U.8.

**Independent direct proof of the odd necessity.** If 5 divides odd n, the odd valuation of 3001 in F_25 persists in F_(n^2), because

\[
v_{3001}(F_{n^2})=1+v_{3001}(n^2/25)=1+2v_{3001}(n).
\]

Primality forces a(n)=3001=s(25), whence n=5 by square-class uniqueness. If odd n>1 is coprime to five, choose a prime q dividing n. Then q is odd and different from five, and q does not divide F_q. One can use the lemma of U.3 with d=q, or the standard congruence `F_q=(5/q) (mod q)`.

If an odd prime r has odd valuation in F_q, then r!=q and

\[
v_r(F_{n^2})=v_r(F_q)+v_r(n^2/q)
             =v_r(F_q)+2v_r(n),
\]

which is odd. If 2 occurs in s(q), then q=3, and both odd indices q and n^2 have Fibonacci valuation one at two. Consequently s(q) divides a(n). The square theorem ensures s(q)>1. Primality of a(n) therefore forces s(q)=s(n^2), impossible for the distinct positive odd indices q<n^2.

The source of the target is https://oeis.org/A250093 , introduced by Vincenzo Librandi on November 12, 2014. The proof above uses the published classical square-class and valuation theorems explicitly; it requires no assumption on the existence or nonexistence of Wall-Sun-Sun primes.

### U.5. Exact trace depths and the WSS obstruction

Let p be prime with p!=2,5, let `epsilon=(5/p)` and `N=p-epsilon`. The Frobenius identities for the original golden algebra give

\[
p\mid F_N,\qquad \varphi^N\equiv\epsilon\pmod p,
\qquad L_N\equiv2\epsilon\pmod p.
\]

Define the positive depth `s_p=v_p(F_N)`. The signed index N is even and positive.

**Theorem.** The two traces retain different depths:

\[
\boxed{v_p(L_N-2\epsilon)=2s_p,\qquad v_p(L_p-1)=s_p.}\tag{U.9}
\]

**Proof.** The discriminant identity gives

\[
(L_N-2\epsilon)(L_N+2\epsilon)=5F_N^2.
\]

The second factor has residue 4*epsilon, hence is a unit modulo p. All factors whose valuations are taken are nonzero: N>0, F_N>0, and the displayed product is positive. Additivity of the valuation gives the first equality.

The Fibonacci-Lucas addition identity gives `2L_p=epsilon*L_N+5F_N`. Therefore

\[
2(L_p-1)(L_N+2\epsilon)
=5F_N(L_N+2\epsilon+\epsilon F_N).
\]

Both parenthesized factors are units modulo p, and 2 and 5 are units. Also L_p>1 for odd primes p. Taking valuations proves the second equality.

**Corollary.** With the standard definition `WSS(p) iff p^2 divides F_N`,

\[
\mathrm{WSS}(p)
\iff p^4\mid L_N-2\epsilon
\iff p^2\mid L_p-1.\tag{U.10}
\]

At normalized first order, dividing in the integers before reducing gives

\[
2\frac{L_p-1}{p}\equiv5\frac{F_N}{p}\pmod p.\tag{U.11}
\]

At the return index N, the trace already has a second-order zero for every p. Its residue modulo p^2 cannot distinguish the WSS primes. The prime-index trace retains the original depth.

### U.6. Half-index parity localization

Set h=N/2. Then `F_N=F_h*L_h`, and `gcd(F_h,L_h)` divides two. Exactly one of F_h,L_h therefore vanishes modulo p.

**Theorem.** The branch is determined by p modulo four:

\[
\begin{array}{ll}
p\equiv1\pmod4:&p\mid F_h,\ p\nmid L_h,\ v_p(F_h)=s_p;\\
p\equiv3\pmod4:&p\mid L_h,\ p\nmid F_h,\ v_p(L_h)=s_p.
\end{array}\tag{U.12}
\]

**Proof.** In the original golden algebra over F_p, put x=phi^h. It satisfies `x^2=epsilon` and `norm(x)=(-1)^h`. If F_h=0 modulo p, x is scalar and `norm(x)=x^2=epsilon`. If L_h=0 modulo p, its conjugate is -x and `norm(x)=-x^2=-epsilon`. Exactly one alternative occurs. Computing the parity of `(p-epsilon)/2` in the two classes of p modulo four selects the stated alternative. The other factor in `F_N=F_h*L_h` is a unit, which proves the exact valuation statements.

**Corollary.** In the first branch WSS(p) is equivalent to `p^2|F_h`; in the second it is equivalent to `p^2|L_h`. Neither branch is excluded by these identities.

### U.7. A first-derivative obstruction to multiple-root lifting

Let p be prime and R=Z/p^2Z. Let rho:R->F_p be the actual reduction homomorphism.

**Lemma.** If rho(a)=rho(b)=0, then ab=0 in R.

**Proof.** Integer representatives of a and b are multiples of p, so their product is a multiple of p^2.

**Theorem.** Suppose f,g in R[X] reduce to `(X-1)^d,(X-1)^e`, respectively, with d,e>=2. Then

\[
fg\ne X^p-1.\tag{U.13}
\]

**Proof.** Reduction commutes with evaluation and formal differentiation. Thus `f(1),f'(1),g(1),g'(1)` all belong to the kernel of rho. The product rule and the lemma give

\[
(fg)'(1)=f'(1)g(1)+f(1)g'(1)=0.
\]

But `(X^p-1)'(1)=p`, which is nonzero in R. Equality of the polynomials is impossible.

**Theorem.** For `2<=d<=p-2` and every f in R[X] reducing to `(X-1)^d`,

\[
\boxed{f\nmid X^p-1.}\tag{U.14}
\]

**Proof.** If a cofactor g existed, reducing and applying Frobenius gives

\[
(X-1)^d\overline g=(X-1)^p\quad\text{in }\mathbb F_p[X].
\]

Since `(X-1)^d` is nonzero, cancellation gives `bar(g)=(X-1)^(p-d)`. The complementary exponent is at least two, contradicting U.13.

**Corollary and boundary.** For every prime p>=5, no polynomial reducing to `(X-1)^2` divides `X^p-1` over R, for any lifted coefficient choice. At p=3 the endpoint has a factor:

\[
X^3-1=(X-1)(X^2+X+1)\quad\text{in }(\mathbb Z/9\mathbb Z)[X].
\]

Its cofactor reduces to a simple root, so U.13 does not apply.

The excluded quadratic lift is the construction proposed in section 4.3 of M. Shi, X. Wang, J. Bouazzaoui, H. K. Kim and P. Sole, *Second order Recurrences, quadratic number fields and cyclic codes*, arXiv:2603.25343v1, https://arxiv.org/html/2603.25343v1 . The theorem excludes all coefficients in that multiple-root construction. The polynomial X^2-X-1 has discriminant five and is separable modulo p for p!=5, so U.14 is not a WSS nonexistence result for the golden unit.

### U.8. Which arithmetic information the square-class argument supplies

The statements U.4-U.8 control the support of odd prime valuations across different Fibonacci indices. They retain the possibly exceptional initial valuation in U.1 rather than assuming it equals one. In particular they remain valid in the presence of WSS primes.

Oddness of a valuation does not distinguish depth one from depth three, and evenness does not distinguish depth two from depth four. The new support bounds therefore do not decide whether `s_p>=2` at some prime p. The existence assertion

\[
\exists p\text{ prime},\ p\ne2,5:\quad p^2\mid F_{p-(5/p)}
\]

and the stronger assertion that there are infinitely many such primes remain distinct unproved statements here. The trace identities locate precisely where that missing depth information is preserved. A further proof must supply a constraint on these prime-index depths that is not already implied by their valuation parity.


## JP. Jacobsthal 最终周期与不动点

### JP.1 原递推、最终周期与从零时刻开始的周期

**定义。** Jacobsthal 数列由

$$
J_0=0,\qquad J_1=1,\qquad J_{n+2}=J_{n+1}+2J_n
$$

确定。对正整数 $m$、正整数 $t$ 与自然数 $N$，定义

$$
\operatorname{TailPeriod}(m,N,t)
\iff \forall n\ge N,\quad m\mid J_{n+t}-J_n.
$$

称 $t$ 为最终周期，若存在 $N$ 使上述关系成立。令 $\rho(m)$ 为最小正最终周期；令 $\mu(m)$ 为存在某个正周期的最早起始下标。最小值的存在性在下文证明。纯周期特指 $N=0$。

**命题。** 对全部 $n\ge0$，

$$
3J_n=2^n-(-1)^n,\qquad
J_{n+1}+J_n=2^n,\qquad
J_{n+1}-2J_n=(-1)^n.\tag{JP1}
$$

**证明。** 令 $S_n=J_{n+1}+J_n$、$D_n=J_{n+1}-2J_n$。原递推给出 $S_{n+1}=2S_n$ 与 $D_{n+1}=-D_n$，且 $S_0=D_0=1$。因此后两式成立；相减得第一式。

**命题。** 令 $G_L(c)$ 是长度 $L$、字母表 $\{0,\ldots,c\}$ 上无相邻非零字母的词数，则

$$
G_0(c)=1,\quad G_1(c)=c+1,\quad
G_{L+2}(c)=G_{L+1}(c)+cG_L(c).
$$

特别地，

$$
G_L(1)=F_{L+2},\qquad G_L(2)=J_{L+2}.\tag{JP2}
$$

**证明。** 按首字母是否为零分解。非零首字母有 $c$ 种选择，第二个字母被迫为零。取基例后，对 $L$ 作二步归纳即得两项特化。

### JP.2 从暂态中分离准确的最终周期

**定理。** 写 $m=2^a u$，其中 $u$ 为正奇数。若 $m>2$ 且 $t>0$，则

$$
\boxed{
\bigl(\exists N:\operatorname{TailPeriod}(m,N,t)\bigr)
\iff 3u\mid 2^t-1.
}\tag{JP3}
$$

右侧成立时，$\operatorname{TailPeriod}(m,a,t)$ 成立。

**证明，必要性。** 取一个起始下标 $N$。将 $n=N$ 与 $n=N+1$ 的周期同余相减，使用 JP1 的第三式，得到

$$
m\mid (-1)^N\bigl((-1)^t-1\bigr).
$$

若 $t$ 为奇数，则 $m\mid2$，与 $m>2$ 矛盾。因此 $t$ 为偶数。JP1 的第一式遂给出

$$
3(J_{N+t}-J_N)=2^N(2^t-1).
$$

左侧被 $3m$ 整除，所以 $3u\mid2^N(2^t-1)$。由于 $u$ 为奇数，$\gcd(3u,2^N)=1$，可在整数整除关系中约去 $2^N$，得到所需结论。

**证明，充分性。** 若 $3u\mid2^t-1$，则降模到 $3$ 可知 $t$ 为偶数。对任意 $n\ge a$，$2^a\mid2^n$，故

$$
3m=3\cdot2^a u\mid2^n(2^t-1)=3(J_{n+t}-J_n).
$$

在整数中约去 $3$ 即得 $m\mid J_{n+t}-J_n$。此处没有在模 $m$ 的环内对非单位 $3$ 作除法。

**定理。** 对 $m=2^a u>2$，

$$
\boxed{\rho(m)=\operatorname{ord}_{3u}(2).}\tag{JP4}
$$

并且 $\rho(1)=\rho(2)=1$。

**证明。** $2$ 与 $3u$ 互素。Euler 定理使得 $2^{\varphi(3u)}\equiv1\pmod{3u}$，所以正最终周期存在。JP3 使其最小值恰为所述乘法阶。模 $1$ 的数列为常数；模 $2$ 时 $J_0=0$，且 $J_n=1$ 对全部 $n\ge1$ 成立。

### JP.3 暂态长度恰等于二进估值

**定理。** 对全部正整数 $m$，

$$
\boxed{\mu(m)=v_2(m).}\tag{JP5}
$$

因此数列模 $m$ 存在纯周期，当且仅当 $m$ 为奇数。

**证明。** JP3 在 $m>2$ 时提供起始下标 $a=v_2(m)$；$m=1,2$ 的上界由前节直接得到。反之，设某个正周期 $t$ 从 $N$ 开始。JP1 的第二式和相邻两个下标的周期同余给出

$$
m\mid2^{N+t}-2^N=2^N(2^t-1).
$$

因为 $2^t-1$ 为奇数，右侧的二进估值恰为 $N$，故 $v_2(m)\le N$。这证明最小起始下标。对于 $m>1$，纯周期情形没有不动点：奇数模数的最小周期由 JP3 为偶数，而偶数模数没有纯周期。

### JP.4 三的幂上的精确阶

**引理。** 对每个正整数 $h$，

$$
\boxed{v_3(4^h-1)=1+v_3(h).}\tag{JP6}
$$

**证明。** 写 $h=3^r w$，其中 $3\nmid w$。几何和

$$
\frac{4^w-1}{4-1}=1+4+\cdots+4^{w-1}\equiv w\not\equiv0\pmod3
$$

表明 $v_3(4^w-1)=1$。若 $x\equiv1\pmod3$，写 $x=1+3z$，则

$$
x^2+x+1=3(1+3z+3z^2),
$$

该因子的三进估值恰为一。因此从 $x-1$ 到 $x^3-1$ 的估值恰增加一。重复 $r$ 次即得结论。

**定理。** 对每个 $b\ge0$，

$$
\boxed{\operatorname{ord}_{3^{b+1}}(2)=2\cdot3^b.}\tag{JP7}
$$

**证明。** 满足 $2^t\equiv1\pmod3$ 的正整数 $t$ 必为偶数，写成 $2h$。JP6 将 $3^{b+1}\mid2^t-1$ 等价为 $3^b\mid h$，故最小正 $t$ 恰为 $2\cdot3^b$。

### JP.5 Benfield–Lippard 猜想 6.3 的最终周期分类

**定理。** 对每个整数 $m>1$，

$$
\boxed{\rho(m)=m\iff\exists k\ge1:\ m=2\cdot3^k.}\tag{JP8}
$$

**证明，必要性。** $m=2$ 时 $\rho(m)=1$，故可设 $m>2$。由 JP3，$\rho(m)$ 为偶数。于是若 $\rho(m)=m$，可写

$$
m=2^a3^b v,\qquad a\ge1,\qquad \gcd(v,6)=1.
$$

由 JP4 与 Euler 定理，

$$
\begin{aligned}
2^a3^b v
&=\rho(m)\\
&\le\varphi(3^{b+1}v)\\
&=2\cdot3^b\varphi(v)\\
&\le2\cdot3^b v\\
&\le2^a3^b v.
\end{aligned}
$$

每一步必须取等号。由于 $v\ge1$，最后一步迫使 $a=1$。又因 $\varphi(v)=v$ 只在正整数 $v=1$ 成立，故 $v=1$。排除 $m=2$ 后，得到 $b\ge1$。

**证明，充分性。** 若 $m=2\cdot3^k$ 且 $k\ge1$，则 JP4 与 JP7 给出

$$
\rho(m)=\operatorname{ord}_{3^{k+1}}(2)=2\cdot3^k=m.
$$

这完成全部模数上的两个方向。最终周期约定与 JP.3 的纯周期结论必须分开使用。

### JP.6 非不动点的减半律与迭代界

**定理。** 若 $m$ 为正偶数且 $\rho(m)\ne m$，则

$$
\boxed{\rho(m)\le m/2.}\tag{JP9}
$$

若 $m>1$ 为奇数，则 $m=3^b$ 时 $\rho(m)=2m$ 且 $2m$ 已是不动点；否则 $\rho(m)<m$。

**证明。** 写 $m=2^a3^b v$，$\gcd(v,6)=1$。若 $v>1$，Euler 定理和 $\varphi(v)$ 为偶数给出：指数

$$
E=3^b\varphi(v)
$$

同时是 $\operatorname{ord}_{3^{b+1}}(2)=2\cdot3^b$ 与 $\operatorname{ord}_v(2)$ 的倍数。由于两个模数互素，$2^E\equiv1\pmod{3^{b+1}v}$。因此

$$
\rho(m)\le E<3^b v=m/2^a.
$$

这同时处理奇数与偶数模数中的 $v>1$ 情形。若 $v=1$，$m>2$ 时 JP7 给出 $\rho(m)=2\cdot3^b$。在偶数非不动点情形，JP8 迫使 $a\ge2$，故 $\rho(m)\le m/2$。余下的 $m=2$ 直接有 $\rho(m)=1$。当 $a=0,b\ge1$，得到 $\rho(3^b)=2\cdot3^b$，而这个值由 JP8 已是不动点。

**推论。** 每个正整数的 $\rho$ 迭代都到达

$$
\{1\}\cup\{2\cdot3^k:k\ge1\}
$$

中的一个不动点，不存在长度大于一的周期轨道。若 $T(m)$ 为首次到达不动点所需的迭代次数，则

$$
\boxed{T(m)\le1+\lfloor\log_2m\rfloor.}\tag{JP10}
$$

**证明。** 偶数轨道在到达不动点前每一步至少减半，且始终为正整数，故终止并至多经历 $\lfloor\log_2m\rfloor$ 步。奇数 $m>1$ 若是三的幂，一步即达不动点；否则第一步变成小于 $m$ 的偶数，再应用减半律。$m=1$ 时 $T(m)=0$。非平凡周期会包含严格下降的偶数步骤，故不可能存在。


## GP3. 黄金三次幂层与 WSS 的素数间深度约束

### GP3.1 经典三次幂层及其确切内容

对 $j\ge1$，定义

$$
n_j=3^j,\qquad
C_j=L_{n_j}^2+1.
$$

**定理。** 有

$$
\boxed{
F_{3n_j}=F_{n_j}C_j,\qquad
C_j+3=5F_{n_j}^2,\qquad
\gcd(C_j,F_{n_j})=1.
}\tag{GP31}
$$

并且

$$
C_1=17,\qquad C_{j+1}=C_j^3+3C_j^2-3.\tag{GP32}
$$

**证明。** 对奇数 $n$，黄金共轭满足 $\varphi^n\psi^n=-1$。展开三次幂差得

$$
F_{3n}=F_n(L_n^2+1).
$$

判别式恒等式 $L_n^2-5F_n^2=-4$ 给出第二式。两个因子的公因子因而整除三；但 $n$ 为奇数时

$$
\gcd(F_n,3)=\gcd(F_n,F_4)=F_{\gcd(n,4)}=F_1=1.
$$

故其最大公因子为一。三次幂和给出 $L_{3n}=L_n^3+3L_n$，再平方加一，得到

$$
(L_n^3+3L_n)^2+1=(L_n^2+1)^3+3(L_n^2+1)^2-3.
$$

首值来自 $L_3=4$。这也是经典序列 A002814 从第三项开始的部分：若该序列按 $a(0)=1,a(1)=2$ 编号，则 $C_j=a(j+1)$。

**定理。** 每个 $C_j$ 为大于一的奇数、不是完全平方数，并且不同 $C_j$ 两两互素。

**证明。** $L_3=4$ 为正偶数，递推 $L_{3n}=L_n^3+3L_n$ 保持正偶性，所以 $C_j$ 为奇数且

$$
L_{n_j}^2<C_j<(L_{n_j}+1)^2.
$$

若 $i<j$，则 $C_i\mid F_{3^{i+1}}\mid F_{3^j}$。GP31 使 $\gcd(C_i,C_j)=1$。这些性质属于经典三次幂数列的算术结构。

### GP3.2 每一层全部素因子的出现秩

令 $\alpha(p)$ 为素数 $p$ 在 Fibonacci 数列中的最小正零下标。

**定理。** 若 $p\mid C_j$ 为素数，则

$$
\boxed{
p\notin\{2,3,5\},\qquad
\alpha(p)=3^{j+1},\qquad p\equiv1\pmod4.
}\tag{GP33}
$$

**证明。** 奇性排除二；GP31 第二式模五为 $C_j\equiv2\pmod5$，排除五。模三同样可用 GP32：$C_1\equiv2$ 且 $2^3+3\cdot2^2-3\equiv2$，故排除三。

由 GP31，$p\mid F_{3^{j+1}}$ 且 $p\nmid F_{3^j}$。出现秩整除任何零下标，因此 $\alpha(p)\mid3^{j+1}$，却不整除 $3^j$。三的幂的约数只有三的幂，故出现秩恰为 $3^{j+1}$。

此外 $L_{n_j}^2\equiv-1\pmod p$。因为 $p$ 为奇素数，其乘法群中有阶为四的元素，因此 $4\mid p-1$。

### GP3.3 实际 WSS 深度等于该层中的素因子重数

记

$$
\epsilon_p=\left(\frac5p\right),\qquad
N_p=p-\epsilon_p,\qquad
s_p=v_p(F_{N_p}).
$$

使用标准 Fibonacci 出现秩定理和估值定理：$\alpha(p)\mid N_p$，且对 $p\ne2,5$，在 $p\mid F_d$ 时

$$
v_p(F_{dk})=v_p(F_d)+v_p(k).
$$

这里的初始估值不预设为一。

**定理。** 对每个素数 $p\mid C_j$，

$$
\boxed{s_p=v_p(C_j).}\tag{GP34}
$$

因此

$$
\boxed{
p\mid C_j\quad\Longrightarrow\quad
\bigl(\mathrm{WSS}(p)\iff p^2\mid C_j\bigr).
}\tag{GP35}
$$

**证明。** GP31 给出

$$
v_p(F_{3^{j+1}})=v_p(C_j).
$$

又由 GP33，$3^{j+1}=\alpha(p)$。令 $h=N_p/\alpha(p)$。因为 $p\nmid N_p$，故 $p\nmid h$。估值定理于是给出

$$
s_p=v_p(F_{\alpha(p)h})=v_p(F_{\alpha(p)})=v_p(C_j).
$$

标准 WSS 条件为 $s_p\ge2$，由此得到第二式。

### GP3.4 每层强迫一个奇初始深度素数

**定理。** 对每个 $j\ge1$，至少存在一个素数 $p_j$ 满足

$$
\boxed{
p_j\mid C_j,\quad
\alpha(p_j)=3^{j+1},\quad
p_j\equiv1\pmod4,\quad s_{p_j}\text{ 为奇数}.
}\tag{GP36}
$$

这些素数在不同层互不相同。

**证明。** $C_j$ 不是完全平方数。唯一素因子分解中必有至少一个素数的指数为奇数。取这样的 $p_j$，由 GP33–GP34 得到全部结论。两两互素性或者不同的出现秩都保证各层所选素数不同。

**定量推论。** 令 $\varphi=(1+\sqrt5)/2$。对 $X\ge\varphi^6$，至少有

$$
\left\lfloor\log_3\left(\frac{\log X}{2\log\varphi}\right)\right\rfloor
\tag{GP37}
$$

个不超过 $X$ 的不同素数，具有三的纯幂出现秩、模四余一且 WSS 初始深度为奇数。

**证明。** 对奇数 $n$，$L_n=\varphi^n-\varphi^{-n}$，故

$$
C_j=\varphi^{2\cdot3^j}+\varphi^{-2\cdot3^j}-1
<\varphi^{2\cdot3^j}.
$$

令 GP37 中的整数为 $K$。对 $1\le j\le K$，有 $C_j<X$。GP36 在每个这样的层给出一个不同的素数 $p_j\le C_j<X$。

### GP3.5 存在性边界

GP36 强迫的是奇数深度，即 $1,3,5,\ldots$。它没有排除所有被选素数都具有深度一。因此 GP36–GP37 并不证明存在 WSS 素数，也不证明存在无穷多个非 WSS 素数。

对本族有精确的受限存在性等价：

$$
\boxed{
\exists j\ge1:\ C_j\text{ 非平方自由}
\iff
\exists p\text{ 为 WSS 素数}:\ \alpha(p)=3^k\text{ 对某个 }k\ge2.
}\tag{GP38}
$$

**证明。** 左向由 GP35。反向若 $\alpha(p)=3^k$ 且 $k\ge2$，则 $p\mid F_{3^k}$ 且 $p\nmid F_{3^{k-1}}$。GP31 使 $p\mid C_{k-1}$，再由 GP34 与 $s_p\ge2$ 得 $p^2\mid C_{k-1}$。

GP38 只处理纯三幂出现秩的素数，不能替代全部素数上的 WSS 存在问题。这条路线要得到 WSS 实例，仍须证明至少一个 $C_j$ 有重复素因子，或证明另一族的同等深度结论。单纯增加奇偶、平方类或固定素数提升恒等式，不能填补这个存在性步骤。

## FD. Fibonacci 素数幂剩余密度的零聚点与 WSS 定量阈值

### FD.1 剩余像与单调性

对素数 p 和整数 k>=1，定义

\[
S_k(p)=\{F_n\bmod p^k:n\ge0\},\qquad
D_k(p)=|S_k(p)|/p^k,\qquad
\delta(p)=\lim_{k\to\infty}D_k(p).
\]

**引理。** 上述极限存在，并满足

\[
0\le\delta(p)\le D_{k+1}(p)\le D_k(p)\le D_1(p)\le\pi(p)/p.
\tag{FD1}
\]

**证明。** 降模映射 S_(k+1)(p)->S_k(p) 满射，每个纤维至多有 p 个元素。故 |S_(k+1)(p)|<=p|S_k(p)|，得到单调性。数列非负，因而收敛。模 p 的全部 Fibonacci 值都在一个长度 pi(p) 的周期中出现，故最后一个不等式成立。

Bragman 和 Rowland 在 *Limiting density of the Fibonacci sequence modulo powers of a prime*, Research in Number Theory 11, 88 (2025), DOI 10.1007/s40993-025-00667-1 的引言中问，是否存在使 delta(p) 任意小的素数。他们的定理 1 还证明每个 delta(p) 为严格正有理数。以下回答前一个问题，只确定零这个聚点。

### FD.2 明确使用的最大素因子定理

对非零整数 M，令 P(M) 为 |M| 的最大素因子，并约定 P(1)=1。记 Phi_n(A,B) 为齐次分圆多项式。Stewart 的定理断言：若 (A+B)^2 与 AB 为非零整数，且 A/B 不是单位根，则存在有效可计算的常数 n_0，使全部 n>n_0 满足

\[
P(\Phi_n(A,B))>
n\exp\!\left(\frac{\log n}{104\log\log n}\right).
\tag{FD2}
\]

这里使用 C. L. Stewart, *On divisors of Lucas and Lehmer numbers*, Acta Mathematica 211 (2013), 291-314, DOI 10.1007/s11511-013-0105-y；arXiv:1008.1274 的定理 1。FD2 是已有定理，不是下文重新证明的结论。

取 A=phi=(1+sqrt(5))/2、B=psi=(1-sqrt(5))/2，则 (A+B)^2=1，AB=-1，且 |A/B|=phi^2>1。全部假设都成立。对 j>=1 令 r_j=3^(j+1)，GP3 中的 C_j 满足

\[
\Phi_{r_j}(\phi,\psi)
=\frac{\phi^{3^{j+1}}-\psi^{3^{j+1}}}
       {\phi^{3^j}-\psi^{3^j}}
=\frac{F_{3^{j+1}}}{F_{3^j}}
=C_j.
\tag{FD3}
\]

分母非零，因为 phi/psi 不是单位根。第一式也可以由
Phi_(3^(j+1))(A,B)=A^(2*3^j)+A^(3^j)B^(3^j)+B^(2*3^j)
直接验证。

### FD.3 零是一个聚点，且小密度对全部精度同时成立

**定理。** 令 p_j=P(C_j)。这些素数互不相同，并满足

\[
\alpha(p_j)=r_j=3^{j+1},\qquad
p_j\equiv1\pmod4,\qquad \pi(p_j)=4r_j.
\tag{FD4}
\]

对全部充分大的 j 及全部 k>=1，

\[
0<\delta(p_j)\le D_k(p_j)
<4\exp\!\left(-\frac{\log r_j}{104\log\log r_j}\right).
\tag{FD5}
\]

特别地，

\[
\boxed{\inf_{p\ {\rm prime}}\delta(p)=0,
\qquad \lim_{j\to\infty}\delta(p_j)=0.}
\tag{FD6}
\]

**证明。** GP33 给出出现秩与模四条件，GP31 给出不同层的互素性，故 p_j 互不相同。令 r=r_j。模 p_j 时 Q^r=cI，其中 c=F_(r-1)，因为 F_r=0。取行列式得到 c^2=(-1)^r=-1，故 c 的阶为四。若 Q^t=I，则 r|t；写 t=rh 后有 Q^t=c^h I，因此四整除 h。这既证明 pi(p_j)=4r，又不引入新的周期约定。

当 r_j>n_0 时，FD2-FD3 给出
p_j>r_j exp(log r_j/(104 log log r_j))。再用 FD1 的
D_k(p_j)<=pi(p_j)/p_j=4r_j/p_j，得到 FD5 的上界。严格正性来自 Bragman-Rowland 的定理 1。由于 log r_j/log log r_j 趋于无穷，右边趋于零，夹逼得到 FD6。

**量词形式。** 对每个 eta>0 和每个素数界 B，都存在素数 p>B，使

\[
0<\delta(p)<\eta,
\qquad \forall k\ge1,\quad D_k(p)<\eta.
\tag{FD7}
\]

**证明。** FD2 使 p_j 趋于无穷，FD5 对 k 的上界独立于 k，故取足够大的同一个 j 即可。

由于所有 delta(p)>0，零是聚点而不是密度值。证明没有假设存在无穷多个 Fibonacci 素数，没有假设所有 Wall 指数等于一，也没有确定全部聚点。

### FD.4 Wall 指数处的周期与两个数值计数

以下 p>=7 为素数，a=alpha(p)，epsilon=(5/p)，e=v_p(F_(p-epsilon))。由出现秩和 U.1，p 不整除 (p-epsilon)/a，因此

\[
e=v_p(F_a),\qquad e\ge1.\tag{FD8}
\]

在 R=Z/(p^e) 中 Q^a=cI，且 c^2=(-1)^a。若 a 为奇数，则 c^2=-1，所以 Q^(2a)=-I 且 pi(p^e)=pi(p)=4a。若 a=2 mod4，则 c=1 modp；由 (c-1)(c+1)=0 modp^e 及 c+1 为单位，得到 c=1 modp^e，故 pi(p^e)=pi(p)=a。若 4|a，则同理 c=-1 modp^e，故 pi(p^e)=pi(p)=2a。这些模 p 的周期三分律是 Vinson 的经典定理，也见 Bragman-Rowland 定理 7；降模保证所给周期没有进一步缩短。

令 r=pi(p)。在 0<=i<r 中去掉 Lucas 零点 L_i=0 modp，记余下的指标集为 I。定义

\[
N_p=|\{F_i\bmod p^e:i\in I\}|.
\]

令 Z_p 为 Lucas 零点 i 的个数，其 F_i modp^e 没有在 I 中出现。Bragman-Rowland 定理 1 给出

\[
\delta(p)=\frac{N_p}{p^e}
+\frac{Z_p}{2p^{2e-1}(p+1)},\qquad 0\le Z_p\le2.
\tag{FD9}
\]

这里 N_p 计不同的数值，Z_p 按该定理计指标，不能互换。Lucas 零点由其命题 9 分类：a 奇数时没有；a=2 mod4 时只有 a/2；4|a 时有 a/2 与 3a/2。

### FD.5 奇偶配对给出严格的计数上界

**定理。** 对每个素数 p>=7，

\[
1\le N_p\le p-1.\tag{FD10}
\]

**证明。** i=0 是 Lucas 非零点并提供值零，故 N_p>=1。由于 F_1,...,F_6 的素因子都不超过五，a>=7。以下全部数值同余都在 R=Z/(p^e) 中进行。使用整数恒等式 F_(-i)=(-1)^(i+1)F_i，将指标视为相应周期的剩余类。

若 a 为奇数，r=4a 且 F_(i+2a)=-F_i。定义保持数值的对合

\[
T(i)=
\begin{cases}
2a-i\pmod{4a},&i\text{ 偶},\\
-i\pmod{4a},&i\text{ 奇}.
\end{cases}
\]

这个对合没有不动点：第一种固定方程要求 i=a 或 3a，与偶性矛盾；第二种要求 i=0 或 2a，与奇性矛盾。因此有 2a 个二元轨道。零值占据两个不同轨道 {0,2a} 与 {a,3a}；此外 F_1=F_2=1，指标一与二因奇偶不同而属于不同轨道。这是两项不同的数值重合，所以 N_p<=2a-2。又 a 为奇数且 a|(p-epsilon)，故 2a<=p-epsilon<=p+1，得到 N_p<=p-1。

若 a=2 mod4，r=a，仅去掉一个 Lucas 零点 a/2。该点不是一或二，因为 a>=7。集合 I 有 a-1 个指标，其中 F_1=F_2，故 N_p<=a-2<=p-1。

若 4|a，r=2a 且 F_(i+a)=-F_i。在偶指标处令 T(i)=a-i mod2a，在奇指标处令 T(i)=-i mod2a。保持数值的计算与第一种相同。其全部不动点恰为 a/2 和 3a/2，正好是删去的两个 Lucas 零点；所以 I 分成 a-1 个二元轨道。因为 a>=8，指标一与二都在 I 中，位于不同奇偶轨道，却有相同值一。于是 N_p<=a-2<=p-1。三种情形覆盖全部情况。

### FD.6 WSS 与随素数移动的密度门槛

**定理。** 对每个素数 p>=7，

\[
\boxed{\mathrm{WSS}(p)\iff e\ge2
\iff \delta(p)<\frac1p.}\tag{FD11}
\]

**证明。** e=1 时，由 FD9、FD10 得 delta(p)>=N_p/p>=1/p。若 e>=2，则

\[
\delta(p)
\le\frac{p-1}{p^2}+\frac{1}{p^3(p+1)}
<\frac1p.
\]

这证明两方向。p=3 可由 F_4=3 和 delta(3)=1 独立处理，得到同一判断；p=2,5 不纳入这里的标准 WSS 定义。

**推论。** 将 delta(p) 写成既约分数 A_p/B_p，B_p>0。对 p>=7，若 Z_p=0，则 v_p(B_p)=e；若 Z_p>0 且 e>=2，则 v_p(B_p)=2e-1；若 e=1，则 v_p(B_p)<=1。因此

\[
\boxed{\mathrm{WSS}(p)\iff p^2\mid B_p.}\tag{FD12}
\]

**证明。** Z_p=0 时，1<=N_p<p 保证 N_p 与 p 互素。Z_p>0 时，通分后的分子为
2N_p p^(e-1)(p+1)+Z_p。
当 e>=2，该分子模 p 为 Z_p，取值一或二，非零，故约分不移除任何 p 因子。当 e=1，原分母 2p(p+1) 的 p 指数为一，约分后至多为一。这些情形给出最后的等价式。

FD6 的零聚点结论没有给出 FD11 所需的移动阈值：它使 delta(p_j) 趋于零，而 WSS 要求 p_j delta(p_j)<1。两者之间不能交换量词或省去因子 p_j。特别地，Stewart 的大小界没有强迫 C_j 出现重复素因子。WSS 存在性和无穷性没有在本节得到证明。

FD3 的最大素因子选择不必等于 GP36 选出的奇重数素因子。本节不声称所选最大素因子的 Wall 指数为奇数。


### FD.7 从精确剩余密度恢复完整初始估值

**定理。** 设 $p\ge7$ 为素数，沿用 FD.4 中的实际 Fibonacci 密度 $\delta(p)$、初始估值 $e=v_p(F_{p-(5/p)})$ 与计数 $N_p,Z_p$。则

$$
\boxed{p^{-e}\le\delta(p)<p^{1-e}.}\tag{FD13}
$$

因而对每个整数 $h\ge1$，

$$
\boxed{e\ge h+1\iff\delta(p)<p^{-h},\qquad
 e=\left\lceil-\frac{\log\delta(p)}{\log p}\right\rceil.}\tag{FD14}
$$

**证明。** FD9 与 $N_p\ge1$ 给出下界。由 $N_p\le p-1$、$Z_p\le2$，

$$
\delta(p)\le\frac{p-1}{p^e}+
 \frac1{p^{2e-1}(p+1)}<\frac p{p^e},
$$

其中严格不等式等价于 $1<p^{e-1}(p+1)$，由 $e\ge1$ 成立。各半开区间 $[p^{-e},p^{1-e})$ 互不相交，立刻得到阈值等价；取对数得到 $e-1<-\log\delta(p)/\log p\le e$，再取上整得到最后一式。

**定理。** 同一精确密度还恢复两个计数：

$$
\boxed{
 N_p=\lfloor p^e\delta(p)\rfloor,\qquad
 Z_p=2p^{e-1}(p+1)\bigl(p^e\delta(p)-N_p\bigr).
}\tag{FD15}
$$

**证明。** FD9 乘以 $p^e$ 得

$$
p^e\delta(p)=N_p+\frac{Z_p}{2p^{e-1}(p+1)}.
$$

末项属于 $[0,1)$，因为 $0\le Z_p\le2$ 且 $p\ge7$、$e\ge1$。取下整得到第一式，移项得到第二式。

因此在 $e\ge1$、$1\le N\le p-1$、$Z\in\{0,1,2\}$ 的参数域内，FD9 的有理数表达对三元组 $(e,N,Z)$ 为单射。对于已给定的精确有理密度，可以反复乘以 $p$，直到第一次达到或超过一；乘法次数就是 $e$，随后用 FD15 恢复 $N,Z$。这不需要数值计算对数。它要求精确密度作为输入，不声称从未带误差界的近似密度恢复这些整数。

FD14 的 $h=1$ 情形是 FD11，其余情形读取全部初始提升深度。它们都是既有密度公式与 FD10 的后果，没有迫使任何素数满足 $e\ge2$。计算密度本身可能需要未知的初始估值，因此该解码结论也不构成绕过 WSS 算术的独立求解算法。


## FSP. 含一的不同 Fibonacci 数之和与 A339621

### FSP.1 正值只计一次与前缀和

令 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$，并定义不同的正 Fibonacci 值集合

$$
\mathcal F_+=\{F_n:n\ge2\}=\{1,2,3,5,8,\ldots\}.
$$

下标从二开始使值一只出现一次。$F_n$ 在 $n\ge2$ 上严格递增。

**引理。** 对每个 $n\ge3$，

$$
\sum_{i=2}^{n-2}F_i=F_n-2.\tag{FSP1}
$$

当 $n=3$ 时左侧为空和。**证明。** 首例两侧为零；从 $n$ 到 $n+1$ 的差为 $F_{n-1}$，由 Fibonacci 递推得到归纳步。

### FSP.2 前驱强迫与完整有限集分类

**定理。** 若 $S\subset\mathcal F_+$ 是有限集且 $1\in S$，则

$$
\boxed{
\sum_{x\in S}x\in\mathcal F_+
\iff
\exists r\ge1:\quad
S=\{1\}\cup\{F_{2j+1}:1\le j<r\}.
}\tag{FSP2}
$$

在成立时 $r$ 唯一，且 $\sum_{x\in S}x=F_{2r}$。

**证明。** 设和为 $F_n$，选其唯一下标 $n\ge2$。若 $n=2$，正性迫使 $S=\{1\}$。若 $n>2$，集合不能含 $F_n$ 或更大的值，因为它还含有不同的正值一。若 $F_{n-1}\notin S$，则 $S$ 中每个值都属于 $\{F_2,\ldots,F_{n-2}\}$，故由 FSP1，

$$
\sum_{x\in S}x\le F_n-2<F_n,
$$

矛盾。因此 $F_{n-1}$ 被迫属于 $S$。$n=3$ 时集合只能为 $\{1\}$，其和为一而 $F_3=2$，所以不存在所需表示。$n\ge4$ 时，$F_{n-1}>1$，删去它仍保留一，余下的和为 $F_{n-2}$。按下标强归纳，目标下标必须是偶数，且连续被迫删去的项恰为 $F_{2r-1},F_{2r-3},\ldots,F_3$，最终剩下 $F_2=1$。这证明必要性及集合形状。

反向，由递推逐项相加得

$$
1+F_3+F_5+\cdots+F_{2r-1}=F_{2r}.
$$

因此所示集合确实有该和。严格递增性给出 $r$ 的唯一性。证明允许相邻下标同时出现，例如 $F_2$ 与 $F_3$；它没有假定 Zeckendorf 的非相邻条件。

### FSP.3 全部正整数上的 Fibonacci 约数和

对正整数 $M$，定义实际约数值集合与和

$$
\mathcal D_F(M)=\{d>0:d\mid M,\ d\in\mathcal F_+\},\qquad
\sigma_F(M)=\sum_{d\in\mathcal D_F(M)}d.
$$

**定理。** 对每个 $M>0$，若 $\sigma_F(M)$ 为 Fibonacci 数，则存在唯一 $r\ge1$，使

$$
\boxed{
\sigma_F(M)=F_{2r},\qquad
\mathcal D_F(M)=\{1\}\cup\{F_{2j+1}:1\le j<r\}.
}\tag{FSP3}
$$

**证明。** $\mathcal D_F(M)$ 是有限的不同正 Fibonacci 值集合，并且因 $1\mid M$ 而包含一。其和为正，因此所给 Fibonacci 值属于 $\mathcal F_+$。应用 FSP2 即得。

**推论，OEIS A339621。** 对每个整数 $m\ge0$，令

$$
a(m)=\sigma_F(m^2+1).
$$

若 $a(m)$ 是 Fibonacci 数，则

$$
\boxed{\exists r\ge1:\quad a(m)=F_{2r}.}\tag{FSP4}
$$

**证明。** $m^2+1>0$，应用 FSP3。这是 Michel Lagneau 于 2020 年 12 月 10 日提出、OEIS A339621 COMMENTS 中标为猜想的命题。证明实际上适用于全部正整数 $M$，不需要 $M=m^2+1$ 或 $3\nmid M$。

FSP4 对值一给出 $1=F_2$，并不否认 $1=F_1$；结论是存在偶下标表示。若允许重复一，$1+1=F_3$ 将破坏结论；若删去必须含一的假设，$\{2,3\}$ 的和为 $F_5$，同样破坏结论。FSP3 没有断言每个偶下标 Fibonacci 数都能由某个 $m^2+1$ 的约数和实现。


## 附录 EMW：Fibonacci 平方中心与非 WSS 秩支持

**定义。** 正整数称为强力数，当且仅当每个素数因子均以至少二次幂出现。令 $F_0=0$、$F_1=1$、$F_{n+2}=F_{n+1}+F_n$。对素数 $p\ne2,5$，定义

$$
\rho(p)=\min\{n\ge1:p\mid F_n\},\qquad
q_p=\frac{F_{p-(5/p)}}p\pmod p.
$$

对 $60\mid M$，定义不同秩组成的集合

$$
\mathcal R_1=\{\rho(p):p\ne2,5\text{ 为素数},\ q_p\ne0\},\qquad
\mathcal R_1(M)=\{r\in\mathcal R_1:\gcd(r,M)\le2\}.
$$

同一秩只计一次。令 EMW 表示不存在连续三个正强力数的命题。

### EMW.1 初始商与简单素因子

记

\[
\varphi^2=\varphi+1,\qquad
\mathcal O_K=\mathbb Z[\varphi],\qquad
\operatorname N(\varphi)=-1.
\]

对素数 \(p\)，定义

\[
\rho(p)=\min\{n\ge1:p\mid F_n\}.
\]

存在性、强整除性与黄金 Frobenius 给出

\[
p\mid F_n\iff\rho(p)\mid n,
\qquad
\rho(p)\mid p-\left(\frac5p\right)\quad(p\ne2,5).
\tag{EMW-B1}
\]

此外 \(\rho(p)\ge3\)，且

\[
\rho(2)=3,\qquad\rho(3)=4,\qquad\rho(5)=5.
\tag{EMW-B2}
\]

**引理 1。** 对 \(p\ne2,5\)，

\[
q_p\ne0\iff v_p(F_{\rho(p)})=1.
\tag{EMW-B3}
\]

**证明。** 写 \(r=\rho(p)\)、\(N=p-(5/p)=kr\)，并在黄金整数中写

\[
\varphi^r=a+b\varphi,
\qquad a=F_{r-1},\quad b=F_r.
\]

有 \(p\mid b\)。范数恒等式模 \(p\) 给出
\(a^2\equiv(-1)^r\pmod p\)，所以 \(p\nmid a\)。又因 \(p\nmid N\)，有 \(p\nmid k\)。在自由基 \(1,\varphi\) 上模 \(p^2\) 展开：

\[
\varphi^N=(a+b\varphi)^k
\equiv a^k+ka^{k-1}b\varphi\pmod{p^2\mathcal O_K}.
\]

高于一次的项都含有 \(b^2\)。比较 \(\varphi\) 坐标，得

\[
F_N\equiv ka^{k-1}F_r\pmod{p^2}.
\]

系数 \(ka^{k-1}\) 模 \(p\) 可逆。因此 \(p^2\mid F_N\) 当且仅当 \(p^2\mid F_r\)，从而得到 (EMW-B3)。证毕。

**推论 2。** 若 \(p\ne2,5\) 且 \(p\parallel F_m\)，则 \(q_p\ne0\)，且 \(\rho(p)\mid m\)。

**证明。** 由 (EMW-B1)，\(r=\rho(p)\mid m\)，再由 Fibonacci 整除性有 \(F_r\mid F_m\)。既然 \(p\mid F_r\) 且 \(p^2\nmid F_m\)，必有 \(p\parallel F_r\)。应用引理 1。证毕。

这里 \(p\parallel A\) 表示 \(p\mid A\) 而 \(p^2\nmid A\)。仅仅知道某个素数整除 \(F_m\) 并不足以推出非 WSS；指数恰为一是必要环节。

### EMW.2 四个相邻指标与连续三元组

**引理 3。** 对 \(n\ge3\)，

\[
F_{n-1}F_{n+1}=F_n^2+(-1)^n,
\qquad
F_{n-2}F_{n+2}=F_n^2-(-1)^n.
\tag{EMW-C1}
\]

若 \(4\mid n\)，则

\[
F_n^2-1=F_{n-2}F_{n+2},\qquad
F_n^2+1=F_{n-1}F_{n+1},
\tag{EMW-C2}
\]

并且两个乘积各自的因子互素。

**证明。** 第一式是 Cassini 恒等式。设 \(A=F_{n-1}\)、\(B=F_n\)，则
\(F_{n-2}=B-A\)、\(F_{n+2}=A+2B\)，所以第二个乘积等于
\(2B^2-A(A+B)=B^2-(-1)^n\)。

若 \(4\mid n\)，则 \(\gcd(n-1,n+1)=1\)、\(\gcd(n-2,n+2)=2\)。强整除性和 \(F_1=F_2=1\) 给出因子的互素性。证毕。

两个强力数的乘积仍为强力数；反之，互素乘积是强力数时，每个因子均为强力数。因此，在 \(4\mid n\)、\(n\ge4\) 时，(EMW-C2) 给出精确对应：

\[
\begin{aligned}
&F_n^2-1,F_n^2,F_n^2+1\text{ 均为强力数}\\
&\quad\iff
F_{n-2},F_{n-1},F_{n+1},F_{n+2}\text{ 均为强力数}.
\end{aligned}
\tag{EMW-C3}
\]

中间的 \(F_n^2\) 本身总是正平方。

### EMW.3 有限素数集合的条件性排除

**定理 4，条件于 EMW。** 给定任意有限素数集合 \(S\)，令

\[
M=\operatorname{lcm}\bigl(60,\{\rho(p):p\in S\}\bigr).
\]

则存在素数 \(p\notin S\cup\{2,5\}\)，使

\[
q_p\ne0,\qquad
\gcd(\rho(p),M)\le2,\qquad
p\le F_{M+2}.
\tag{EMW-D1}
\]

**证明。** 对每个 \(p\in S\) 及 \(s\in\{-2,-1,1,2\}\)，\(\rho(p)\mid M\) 且 \(\rho(p)\ge3\)，故 \(\rho(p)\nmid M+s\)。由 (EMW-B1)，\(p\nmid F_{M+s}\)。

EMW 排除中心 \(F_M^2\) 的强力数三元组，故至少一个外侧数不是强力数。由 (EMW-C2)，四个相邻 Fibonacci 数中至少一个有简单素因子 \(p\)。\(M\) 被 60 整除，也排除了秩分别为 3、4、5 的素数 2、3、5。推论 2 给出 \(q_p\ne0\)。

由 \(\rho(p)\mid M+s\) 得 \(\gcd(\rho(p),M)\mid s\)，因此最大公约数不超过 2。最后，\(p\mid F_{M+s}\le F_{M+2}\)。证毕。

### EMW.4 无限周期并集的密度

记 \(\mathcal S=\{-2,-1,1,2\}\)。对 \(60\mid M\)、\(r\ge3\)，定义

\[
E_r(M)=\{k\ge1:\exists s\in\mathcal S,\ r\mid Mk+s\}.
\]

**引理 5，单个秩。** 若 \(g=\gcd(r,M)>2\)，则 \(E_r(M)\) 为空。若 \(g\le2\)，则它是有限个模 \(r/g\) 的剩余类的并，且其自然密度满足

\[
d(E_r(M))\le\frac4r.
\tag{EMW-E1}
\]

**证明。** 线性同余 \(Mk\equiv-s\pmod r\) 有解当且仅当 \(g\mid s\)；有解时，恰对应一个模 \(r/g\) 的剩余类。若 \(g=1\)，至多有四个类，各密度 \(1/r\)。若 \(g=2\)，只有 \(s=\pm2\) 可能，每个类密度 \(2/r\)。若 \(g>2\)，四个同余都无解。证毕。

**引理 6，可求和尾项。** 设 \(D\subseteq\{3,4,\ldots\}\)，且

\[
\sum_{r\in D}\frac1r<\infty.
\]

则 \(E_D(M)=\bigcup_{r\in D}E_r(M)\) 有自然密度，并且

\[
d(E_D(M))\le
4\sum_{\substack{r\in D\\\gcd(r,M)\le2}}\frac1r.
\tag{EMW-E2}
\]

**证明。** 先取任意有限 \(T\subset D\)。有限并 \(E_T(M)\) 是周期集合，故有自然密度；由有限次并集上界及引理 5，满足相应的有限和估计。

不能直接假设自然密度对可数并次可加。为处理尾项，对整数 \(X\ge1\) 使用下面的有限计数：

\[
\#\left(\left(\bigcup_{r\in D\setminus T}E_r(M)\right)\cap[1,X]\right)
\le4(MX+2)\sum_{r\in D\setminus T}\frac1r.
\tag{EMW-E3}
\]

事实上，对固定 \(s\)，映射 \(k\mapsto Mk+s\) 在 \(1\le k\le X\) 上为正且单射，其像包含于 \([1,MX+2]\)。其中被 \(r\) 整除的数至多 \(\lfloor(MX+2)/r\rfloor\) 个。对四个 \(s\) 以及所有尾部 \(r\) 求和即得 (EMW-E3)。在任意固定的 \(X\) 上，\(r>MX+2\) 根本没有贡献。

固定 \(M\) 后，(EMW-E3) 除以 \(X\) 并取上极限，所得误差至多
\(4M\sum_{r\in D\setminus T}1/r\)，它随着有限集合 \(T\) 穷尽 \(D\) 而趋零。因此无限并的上下密度均趋向有限周期并密度的同一极限。自然密度存在；再让有限并中的求和穷尽，得到 (EMW-E2)。证毕。

证明没有使用各个秩、素数或剩余类之间的独立性。选择 \(M\) 与让尾项趋零分属两个步骤：应用引理时，\(M\) 已经固定。

### EMW.5 可求和秩支持的密度放大

定义

\[
\mathcal T=\{n\ge3:F_n^2-1,F_n^2,F_n^2+1\text{ 均为强力数}\}.
\]

对正整数集合 \(A\)，下渐近密度记为

\[
\underline d(A)=\liminf_{X\to\infty}\frac{\#(A\cap[1,X])}{X}.
\]

**定理 7。** 若对某个 \(60\mid M_0\)，

\[
\sum_{r\in\mathcal R_1(M_0)}\frac1r<\infty,
\tag{EMW-F1}
\]

则对每个 \(0<\eta<1\)，存在 \(M_0\mid M\)，使

\[
\underline d\{k\ge1:Mk\in\mathcal T\}\ge1-\eta.
\tag{EMW-F2}
\]

特别地，\(\underline d(\mathcal T)>0\)。

**证明。** 从 (EMW-F1) 选有限 \(T\subset\mathcal R_1(M_0)\)，使

\[
\sum_{r\in\mathcal R_1(M_0)\setminus T}\frac1r<\frac\eta4.
\]

令 \(M=\operatorname{lcm}(M_0,T)\)。若 \(r\in\mathcal R_1(M)\)，则由 \(M_0\mid M\)，有 \(r\in\mathcal R_1(M_0)\)。它不可能属于 \(T\)，因为此时 \(r\mid M\)，而 \(r\ge3\) 会违反 \(\gcd(r,M)\le2\)。所以

\[
\mathcal R_1(M)\subseteq\mathcal R_1(M_0)\setminus T,
\qquad
\sum_{r\in\mathcal R_1(M)}\frac1r<\frac\eta4.
\]

对固定的这个 \(M\)，应用引理 6，得到

\[
d\left(\bigcup_{r\in\mathcal R_1(M)}E_r(M)\right)<\eta.
\]

考虑不属于这个并集的 \(k\)。如果某个 \(F_{Mk+s}\) 不是强力数，则它有简单素因子 \(p\)。由 \(60\mid M\) 与 (EMW-B2)，\(p\) 不会是 2、3、5。由推论 2，\(r=\rho(p)\in\mathcal R_1\)；又因为 \(r\mid Mk+s\)，有 \(\gcd(r,M)\le2\)，从而 \(r\in\mathcal R_1(M)\) 且 \(k\in E_r(M)\)，矛盾。

因此这四个 Fibonacci 数都是强力数，(EMW-C2) 给出 \(Mk\in\mathcal T\)。此类 \(k\) 的下密度至少为 \(1-\eta\)，即 (EMW-F2)。

最后，将等差数列中的计数换回全部指标：

\[
\underline d(\mathcal T)\ge\frac{1-\eta}{M}>0.
\]

证毕。

### EMW.6 条件性秩发散与秩素因子限制

**定理 8。** 若 \(\underline d(\mathcal T)=0\)，则对每个 \(60\mid M\)，

\[
\boxed{\sum_{r\in\mathcal R_1(M)}\frac1r=\infty.}
\tag{EMW-G1}
\]

**证明。** 若有一个这样的级数收敛，定理 7 给出 \(\underline d(\mathcal T)>0\)，矛盾。证毕。

EMW 使 \(\mathcal T\) 为空，故是定理 8 的充分条件。即使允许存在无限多个强力数三元组，只要此 Fibonacci 平方切片的指标集合下密度为零，结论仍然成立。所有整数高度中的零密度并不自动意味着这一指标密度条件。

**推论 9。** 在定理 8 的前提下，对每个 \(60\mid M\)，

\[
\sum_{\substack{p\ne2,5\text{ 素数}\\q_p\ne0\\\gcd(\rho(p),M)\le2}}
\frac1{\rho(p)}=\infty.
\tag{EMW-G2}
\]

**证明。** 为每个 \(r\in\mathcal R_1(M)\) 选择一个支持该秩的素数 \(p_r\)。不同秩必对应不同素数，故左侧至少包含 (EMW-G1) 中的全部项。证毕。

(EMW-G1) 比 (EMW-G2) 更强，因为它没有利用同一秩对应的多个素数来重复增加级数。两式均没有声称 \(\sum1/p\) 发散。

**推论 10，避开任意有限的小素因子。** 给定整数 \(B\ge5\)，令

\[
M_B=\operatorname{lcm}(60,1,2,\ldots,B).
\]

在定理 8 的前提下，存在无限多个非 WSS 素数，其不同秩满足 (EMW-G1)，且每个这样的秩 \(r\) 都有

\[
r>B,\qquad4\nmid r,\qquad
q\mid r,\ q\text{ 为奇素数}\Longrightarrow q>B.
\tag{EMW-G3}
\]

**证明。** 每个 \(q\le B\) 的奇素数都整除 \(M_B\)，而 \(4\mid M_B\)。因此 \(\gcd(r,M_B)\le2\) 排除了这些奇素因子及因子 4。如果 \(3\le r\le B\)，则 \(r\mid M_B\)，同样矛盾。应用定理 8。证毕。

该族允许奇秩及二倍奇秩，未限制秩必须为素数，也未限制素数 \(p\) 在黄金域中惰性或分裂。



## 附录 EMWS：四个线性形式的筛与平方自由的非 WSS 秩

### EMWS.1 线性形式与四维分布

**定义。** 沿用附录 EMW 的 Fibonacci 数列、实际初始商 $q_p$、出现秩 $\rho(p)$、不同非 WSS 秩集合 $\mathcal R_1$ 与强力数三元组指标集合 $\mathcal T$。在本附录中，$\log$ 表示自然对数。令

$$
Q(k)=(60k-1)(60k+1)(30k-1)(30k+1),\qquad k\ge1.
$$

**引理。** 四个线性因子的值两两互素，且均与 $30$ 互素。对每个素数 $t>5$，$Q$ 模 $t$ 恰有四个不同的根，模 $t^2$ 也恰有四个不同的根。

**证明。** 同一斜率的两个值相差二，交叉斜率的整数线性组合为 $1,-1,3,-3$；全部值均为奇数且不被三、五整除，故两两互素。模 $t$ 的根为 $\pm60^{-1},\pm30^{-1}$。同组根重合会使 $t\mid2$；跨组重合会使 $t\mid1$ 或 $t\mid3$，均不可能。每个斜率模 $t^2$ 可逆，故各根唯一提升。模 $t$ 不同保证提升后仍不同。

**引理。** 对平方自由的 $d$ 且 $\gcd(d,30)=1$，有

$$
\#\{1\le k\le X:d\mid Q(k)\}
=\frac{4^{\omega(d)}}dX+R_d(X),\qquad
|R_d(X)|\le4^{\omega(d)}.\tag{EMWS1}
$$

**证明。** 中国剩余定理给出恰好 $4^{\omega(d)}$ 个模 $d$ 的根。每个剩余类在 $[1,X]$ 内的计数与 $X/d$ 相差至多一。对根求和即得。

**定理，四维下界筛的应用。** 令 $a=4/35$。存在 $c_0>0$，使全部充分大的整数 $X$ 满足

$$
\#\{1\le k\le X:t\mid Q(k),\ t\text{ 素数}\Longrightarrow t\ge X^a\}
\ge c_0\frac{X}{(\log X)^4}.\tag{EMWS2}
$$

**证明。** 对素数集合 $t>5$ 使用 C. S. Franze, *Sifting Limits for the $\Lambda^2\Lambda^-$ Sieve*, Theorem 1, arXiv:1012.3809, https://arxiv.org/pdf/1012.3809 。该定理的四维参数为 $8.522$。验证其假设如下：EMWS1 给出 $f(t)=t/4$；Mertens 素数求和式给出

$$
\sum_{5<t<z}\frac{\log t}{f(t)}=4\log z+O(1).
$$

取 $D=X/(\log X)^{40}$。该定理所需的加权余项满足

$$
\sum_{\substack{d<D\ (d,30)=1}}\mu^2(d)7^{\omega(d)}|R_d(X)|
\le\sum_{d<D}\mu^2(d)28^{\omega(d)}
\le\sum_{d<D}\tau_{28}(d)
\ll D(1+\log D)^{27}
\ll\frac{X}{(\log X)^{13}}.\tag{EMWS3}
$$

这里 $\tau_{28}$ 计有序的二十八因子分解；其和的上界可由先固定二十七个因子、再以 $D$ 除以前面因子的乘积控制最后一因子得到。四维所需误差为 $O(X/(\log X)^5)$，故 EMWS3 充分。$Q(k)$ 随正整数 $k$ 严格递增，所以所筛序列恰有 $X$ 项。Franze 定理给出筛界 $z=X^{1/8.522}$；因 $4/35<1/8.522$，减小筛界的单调性得到 EMWS2。素数二、三、五不整除任何 $Q(k)$，无需加入筛集。

### EMWS.2 平方自由与最多八个素因子

**定义。** 对整数 $X\ge2$，令 $y=X^{4/35}$，并定义

$$
\mathcal A_X=\{1\le k\le X:Q(k)\text{ 平方自由，且其全部素因子}\ge y\}.
$$

**定理。** 存在 $c>0$，使全部充分大的 $X$ 满足

$$
|\mathcal A_X|\ge c\frac{X}{(\log X)^4}.\tag{EMWS4}
$$

对每个 $k\in\mathcal A_X$，四个线性因子各自至多包含八个素因子。

**证明。** 在 EMWS2 的集合内，若 $t^2\mid Q(k)$，则 $t\ge y>5$。两两互素性迫使 $t^2$ 整除某一个线性因子，因此 $t\le\sqrt{60X+1}$。每个线性形式模 $t^2$ 只有一个根，故删去的指标数至多

$$
4\sum_{\substack{y\le t\le\sqrt{60X+1}\ t\text{ 素数}}}
\left(\frac{X}{t^2}+1\right)
\ll \frac{X}{y}+\sqrt X
=o\left(\frac{X}{(\log X)^4}\right).\tag{EMWS5}
$$

这证明 EMWS4。若某一个线性因子包含至少九个素因子，则它至少为 $y^9=X^{36/35}$，但它至多为 $60X+1$，对充分大的 $X$ 矛盾。平方自由性使这里的不同素因子数和按重数计的素因子数相同。

### EMWS.3 无条件的关联计数不等式

**定义。** 对正整数 $r$，令 $r_{\rm odd}=r/2^{v_2(r)}$。令 $\mathcal R_8(X)$ 为满足下列条件的不同秩 $r\in\mathcal R_1$ 的集合：

$$
r\le60X+2,\quad r\text{ 平方自由},\quad\gcd(r,60)\le2,\quad
1\le\omega(r_{\rm odd})\le8,
$$

且 $r_{\rm odd}$ 的每个素因子均不小于 $y=X^{4/35}$。记

$$
R_8(X)=|\mathcal R_8(X)|,\qquad
T_X=\#\{k\in\mathcal A_X:60k\in\mathcal T\}.
$$

**定理。** 对全部充分大的 $X$，

$$
\boxed{
T_X+\frac{8X}{y}R_8(X)
\ge |\mathcal A_X|
\ge c\frac{X}{(\log X)^4}.
}\tag{EMWS6}
$$

**证明。** 取 $k\in\mathcal A_X$ 且 $60k\notin\mathcal T$。EMW-C3 给出某个 $s\in\{-2,-1,1,2\}$，使 $F_{60k+s}$ 具有简单素因子 $p$。由于素数二、三、五的出现秩分别为三、四、五，而 $60k+s$ 均不被这些秩整除，所以 $p\notin\{2,3,5\}$。EMW-B3 给出 $q_p\ne0$ 及 $r=\rho(p)\mid60k+s$。

四个指标为 $60k-1,60k+1,2(30k-1),2(30k+1)$。因此 $r$ 平方自由，$\gcd(r,60)\le2$，且其奇部整除一个平方自由的线性因子。秩至少为三，故奇部大于一；EMWS.2 给出其素因子数至多八，且每个素因子均至少为 $y$。故 $r\in\mathcal R_8(X)$，并有 $r\ge y$。

固定一个这样的 $r$，令 $g=\gcd(r,60)$。若 $g=1$，至多四个模 $r$ 的类能满足 $r\mid60k+s$；若 $g=2$，只有两个模 $r/2$ 的类。因而在 $1\le k\le X$ 中，一个秩至多对应

$$
\frac{4X}{r}+4\le\frac{8X}{y}
$$

个指标，其中使用 $r\ge y$ 与 $y\le X$。对每个 $k$ 选择一个见证秩，再按不同秩合并计数，得到 $|\mathcal A_X|-T_X\le(8X/y)R_8(X)$。EMWS4 给出第二个不等式。证明未假设不同秩的剩余类独立或互不重叠。

### EMWS.4 条件性非 WSS 素数族与定量界

**定理。** 若 $T_X=o(X/(\log X)^4)$，则

$$
\boxed{R_8(X)\gg\frac{X^{4/35}}{(\log X)^4}}\tag{EMWS7}
$$

对全部充分大的 $X$ 成立。EMW 是该前提的充分条件。

**证明。** EMWS6 中用 $T_X\le(c/2)X/(\log X)^4$，移项后除以 $8X/y$。EMW 排除所有强力数三元组，故 $T_X=0$。

**推论。** 在同一前提下，存在常数 $c_1>0$，使全部充分大的 $x$ 满足

$$
\#\left\{p\le x:\begin{array}{l}
p\ne2,5\text{ 为素数},\ q_p\ne0,\\
\rho(p)\text{ 平方自由},\ \gcd(\rho(p),60)\le2,\\
1\le\omega(\rho(p)_{\rm odd})\le8
\end{array}\right\}
\ge c_1\frac{(\log x)^{4/35}}{(\log\log x)^4}.\tag{EMWS8}
$$

**证明。** 每个 $r\in\mathcal R_8(X)$ 都有一个实际的非 WSS 素数支持。不同秩的支持素数不同。由于该素数整除 $F_r$，它至多为 $F_{60X+2}\le2^{60X+2}$。取 $X=\lfloor\log x/(120\log2)\rfloor$，则充分大的 $x$ 满足 $2^{60X+2}\le4\sqrt x\le x$。应用 EMWS7 并用 $X\asymp\log x$ 即得。

**推论。** 在同一前提下，可选出无限多个非 WSS 素数，使其出现秩的奇部大于一、平方自由、各至多有八个素因子，并且这些奇部两两互素。

**证明。** 已选有限多个秩后，取 $X$ 足够大，使 $X^{4/35}$ 大于所有先前奇部的素因子。EMWS7 保证新集合非空。其任何秩的奇部全部由更大的素数组成，因此与先前全部奇部互素。递归选择完成证明。

EMWS7 的前提是薄筛集上的相对计数条件。一般集合的下密度为零并不蕴含其计数为 $o(X/(\log X)^4)$，因此附录 EMW 的 $\underline d(\mathcal T)=0$ 不能单独替代本节前提。上述族没有限制出现秩为素数，也没有限制支持素数在黄金域中的分裂类型。


## Appendix FDS. Exact Fibonacci-divisor spectra at square-plus-one values

### FDS.1. A two-factor non-mixing theorem

**Definition.** For a positive integer N, let D_F(N) be the set of distinct positive Fibonacci values dividing N. The value F_1=F_2=1 is included once. Let tau(N) be the number of positive divisors of N.

**Lemma.** For positive K and nonnegative A,B,

$$
K\mid AB\quad\Longleftrightarrow\quad
K\mid\gcd(K,A)\gcd(K,B).\tag{FDS1}
$$

**Proof.** For each prime power p^e exactly dividing K, the right side asserts min(e,v_p(A))+min(e,v_p(B))>=e. This is equivalent to v_p(A)+v_p(B)>=e. If A or B is zero, both divisibility statements hold, so those cases require no valuation at zero.

**Lemma.** For k>=3,

$$
F_{\lfloor k/2\rfloor}^2<F_k.\tag{FDS2}
$$

**Proof.** The case k=3 is 1<2. Otherwise put m=floor(k/2)>=2. Fibonacci addition gives F_(2m)=F_(m-1)F_m+F_mF_(m+1)>F_m^2, using positivity and F_(m+1)>=F_m. Monotonicity and 2m<=k finish the proof.

**Theorem.** For all natural a,b and all k>=3,

$$
\boxed{F_k\mid F_aF_b\quad\Longleftrightarrow\quad k\mid a\ \lor\ k\mid b.}\tag{FDS3}
$$

**Proof.** The reverse implication is Fibonacci divisibility. Suppose the left side holds, but neither index is divisible by k. Put d=gcd(k,a), e=gcd(k,b). These are positive proper divisors of k, hence d,e<=floor(k/2). By FDS1 and strong Fibonacci divisibility, F_k divides F_dF_e. This positive product is at most F_floor(k/2)^2, contradicting FDS2. No coprimality hypothesis is needed.

**Boundary proposition.** FDS3 does not extend to three factors, and its lower bound on k cannot be dropped.

**Proof.** F_6=8=F_3^3, although 6 does not divide 3. Also F_2=1 divides F_1F_1, although 2 does not divide 1.

### FDS.2. The complete A340542 divisor set and count

**Theorem.** For even n>=2 put (u,v)=(n-1,n+1); for odd n>=3 put (u,v)=(n-2,n+2). Then

$$
\boxed{D_F(F_n^2+1)=\{1\}\cup\{F_d:d\ge3,\ d\mid u\text{ or }d\mid v\},}\tag{FDS4}
$$

$$
\boxed{|D_F(F_n^2+1)|=\tau(u)+\tau(v)-1.}\tag{FDS5}
$$

The values at n=0,1 are respectively 1,2.

**Proof.** Cassini and the Fibonacci recurrence give F_(n-1)F_(n+1)=F_n^2+(-1)^n and F_(n-2)F_(n+2)=F_n^2-(-1)^n. Thus F_n^2+1=F_uF_v in the stated cases. Apply FDS3 to every k>=3; the value one is always a divisor. The u,v are positive odd coprime integers, so their positive divisor sets overlap only at one. All their remaining divisors are at least three, where Fibonacci values are distinct. Counting the union proves FDS5. At n=0 the target is one, and at n=1 it is two.

These are explicit formulas for the sequence defined by Michel Lagneau in OEIS A340542, https://oeis.org/A340542 . The definition counts divisor values rather than Fibonacci indices.

### FDS.3. The factor-five rigidity and even Lucas indices

**Theorem.** If u,v are positive odd coprime integers and k>=3, then

$$
\boxed{F_k\mid5F_uF_v\quad\Longleftrightarrow\quad
k=5\ \lor\ k\mid u\ \lor\ k\mid v.}\tag{FDS6}
$$

**Proof.** The reverse implication is immediate. If 5 does not divide F_k, cancel the factor five and apply FDS3. Otherwise the rank-five identity 5|F_k iff 5|k holds. Exclude k=5, so k>=10, and suppose neither u nor v is divisible by k. Set d=gcd(k,u), e=gcd(k,v). They are odd coprime proper divisors of k. Since F_u,F_v are coprime, the elementary prime-exponent formula for a gcd gives

$$
F_k=\gcd(F_k,5F_uF_v)
\le5\gcd(F_k,F_uF_v)=5F_dF_e.\tag{FDS7}
$$

If d=1 or e=1, the remaining proper divisor is at most floor(k/2), so F_dF_e<=F_floor(k/2). Otherwise d,e are distinct odd integers at least three and five. Their product divides k, and 2(d+e-1)<=de<=k. Fibonacci addition yields F_dF_e<=F_(d+e-1)<=F_floor(k/2). Write m=floor(k/2)>=5. Since k>=m+4,

$$
F_k\ge F_{m+4}=3F_m+2F_{m+1}>5F_m,
$$

contradicting FDS7. This proves necessity.

**Theorem.** For every even n>=2,

$$
\boxed{D_F(L_n^2+1)=D_F(F_n^2+1)\cup\{5\},}\tag{FDS8}
$$

$$
\boxed{|D_F(L_n^2+1)|=
\tau(n-1)+\tau(n+1)-1+\mathbf1_{5\nmid(n^2-1)}.}\tag{FDS9}
$$

At n=0 the count is two.

**Proof.** The golden trace-norm identity gives L_n^2-5F_n^2=4 for even n, hence L_n^2+1=5(F_n^2+1). Use FDS6 with u=n-1,v=n+1 and compare with FDS4. The value five is already present exactly when 5 divides u or v, equivalently 5 divides n^2-1. At zero, L_0^2+1=5 has Fibonacci divisor values one and five.

The modulo-five comparison in FDS8 is already recorded in OEIS A340542's comments, together with the comparison to A339669. FDS4-FDS9 give its full divisor-index derivation and explicit counts.


## Appendix ZBD. Largest-index-prime descent and fully exceptional WSS blocks

### ZBD.1. Preservation of actual initial depth

**Definition.** For primes p other than two and five, let rho(p) be the least positive Fibonacci zero index, h_p=v_p(F_rho(p)), and q_p=F_(p-(5/p))/p modulo p. A prime-index block is the set of prime divisors of F_ell, where ell>=7 is prime. Call the block fully exceptional when every such divisor has q_p=0.

The classical rank and valuation identities, as stated in U.1 and EMW.1, give rho(p)|p-(5/p), q_p=0 iff h_p>=2, and

$$
v_p(F_{dt})=v_p(F_d)+v_p(t)\quad\text{when }p\mid F_d.
$$

They retain the unknown initial depth.

**Theorem.** Let m>1, and suppose its largest prime factor ell is at least seven. For every prime p dividing F_ell,

$$
\boxed{\rho(p)=\ell,\quad p>\ell,\quad p\nmid m,\quad
v_p(F_m)=v_p(F_\ell)=h_p.}\tag{ZBD1}
$$

**Proof.** The prime ell is neither three nor five, so Fibonacci parity and the rank of five exclude p=2,5. Since rho(p)|ell and F_1=1, the rank is ell. The rank bound forces ell|p-1 or ell|p+1. If p<=ell, the first alternative is impossible, and the second forces p=ell-1, an even integer greater than two. Hence p>ell and p does not divide m. Apply the valuation formula to d=ell,t=m/ell. Its last summand vanishes.

**Corollary.** Under ZBD1, if F_m is powerful, then F_ell is powerful and its entire prime-index block is fully exceptional.

**Proof.** Every prime dividing F_ell also divides F_m. Its exponent is unchanged by ZBD1, so it is at least two. The equality with h_p and the standard initial-quotient criterion prove the final assertion.

**Proposition.** Every powerful block F_ell with prime ell>=7 contains a prime p of rank ell and odd initial depth at least three.

**Proof.** The classical Fibonacci square classification gives F_n square only at n=0,1,2,12. In particular F_ell is not square. Its prime factorization has an odd exponent; powerfulness makes that exponent at least three. ZBD1, or the prime-rank argument in its proof, identifies this exponent with h_p. The square theorem is the classical result stated in P. Ribenboim, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), section 3.4, https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf .

### ZBD.2. Four fully exceptional blocks at a failing window

Retain the definitions Q(k), y=X^(4/35), A_X, T_X and R_8(X) from EMWS. Let

$$
H(X)=\#\{\ell\text{ prime}:y\le\ell\le60X+1,\ F_\ell\text{ powerful}\}.
$$

**Theorem.** For sufficiently large X, each k counted by T_X forces four distinct fully exceptional prime-index blocks, at indices at least y. Each block contains an odd-depth-at-least-three WSS prime; these four witness primes are distinct.

**Proof.** The four adjacent Fibonacci terms are powerful by EMW-C3. Take the largest prime factor of each of 60k-1,60k+1,30k-1,30k+1. The linear forms are pairwise coprime, so their four largest prime factors are distinct. All are at least y>5. For an adjacent even index, its largest prime factor is the largest prime factor of its odd half. Apply ZBD1 to the four adjacent indices and then its corollary. Distinct prime indices give coprime Fibonacci numbers by strong divisibility; alternatively a witness cannot have two different least ranks. The preceding proposition supplies the odd-depth witnesses.

**Theorem.** For sufficiently large X,

$$
\boxed{4T_X\le\frac{8X}{y}H(X),}\tag{ZBD2}
$$

and consequently

$$
\boxed{8R_8(X)+2H(X)\ge\frac yX|\mathcal A_X|
\ge c\frac{X^{4/35}}{(\log X)^4}.}\tag{ZBD3}
$$

**Proof.** Count all four distinct incidences from each failing window. A fixed ell>5 divides one of the four forms at no more than 4X/ell+4<=8X/y values of k. Only the H(X) fully exceptional indices can occur in these incidences. This proves ZBD2. Substitute T_X<=(2X/y)H(X) in EMWS6 and multiply by y/X. The final lower bound is EMWS4, which explicitly uses Franze's established four-dimensional lower-bound sieve.

**Corollary.** If H(X)=o(X^(4/35)/(log X)^4), then R_8(X)>>X^(4/35)/(log X)^4, so the non-WSS prime-family bound EMWS8 follows without assuming EMW.

**Proof.** Absorb 2H(X) in the rightmost lower bound of ZBD3 and apply the same passage from ranks to supporting primes as in EMWS.4.

**Proposition.** Let D_3(X) count distinct prime indices ell in [y,60X+1] for which some p of rank ell has odd h_p>=3. Then H(X)<=D_3(X), and ZBD3 remains true with H(X) replaced by D_3(X).

**Proof.** Each H block supplies such a witness by ZBD.1. This is an inclusion of sets of indices, so no repeated counting of supporting primes is involved.

ZBD3 is a disjunction concerning the actual zero and nonzero initial-quotient supports. It does not assert that either term alone has the displayed order of growth. No estimate on H(X) or D_3(X) is assumed implicitly, and no failing window or WSS witness is asserted to exist by these implications.


## Appendix PBC. Prime-block completeness, depth towers, and exact support partition

### PBC.1. Complete powerful classification on five-smooth indices

**Definition.** A positive integer is powerful when every prime divisor occurs with exponent at least two. In particular one is powerful. Let E={1,2,6,12}. A positive integer is five-smooth when all of its prime divisors belong to {2,3,5}.

**Theorem.** For every positive five-smooth integer m,

$$
\boxed{F_m\text{ powerful}\quad\Longleftrightarrow\quad m\in E.}\tag{PBC1}
$$

**Proof.** Write m=2^a3^b5^c. If c=1, the classical identity v_5(F_m)=v_5(m) gives a simple prime divisor five. If c>=2, use F_25=5^2*3001. The integer 3001 is prime: no integer from two through 54 divides it, while sqrt(3001)<55. Since 3001 does not divide m, the valuation formula U.1 gives v_3001(F_m)=v_3001(F_25)+v_3001(m/25)=1. Thus powerfulness forces c=0.

If b>=2, the identity F_9=2*17 and 17 not dividing m give v_17(F_m)=1. Thus b<=1. If a>=3, the identity F_8=3*7 and seven not dividing m give v_7(F_m)=1. Thus a<=2. The remaining indices are 1,2,3,4,6,12. The values F_3=2 and F_4=3 are not powerful, whereas F_1=F_2=1, F_6=8 and F_12=144 are powerful. This proves both directions. The valuation formula used here is Lengyel's theorem, as stated in Medina and Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Theorem 1.4, https://arxiv.org/abs/0910.2907 .

### PBC.2. Prime-index completeness and the least counterexample

**Theorem.** The following assertions are equivalent:

$$
\begin{aligned}
\mathrm{(A)}&\quad \forall m\ge1,\quad F_m\text{ powerful}\Longrightarrow m\in E;\\
\mathrm{(B)}&\quad \forall\ell\ge7\text{ prime},\quad F_\ell\text{ is not powerful}.
\end{aligned}\tag{PBC2}
$$

If (A) is false, its least counterexample index is prime and at least seven.

**Proof.** Assertion (A) implies (B), since no prime at least seven belongs to E. Conversely suppose F_m is powerful and m is outside E. By PBC1, m has a prime factor at least seven. Let ell be its largest prime factor. ZBD1 shows that every prime p dividing F_ell has rank ell, exceeds ell, does not divide m, and satisfies v_p(F_m)=v_p(F_ell). Consequently F_ell is powerful. This contradicts (B), proving equivalence. If m is the least counterexample, ell is another counterexample with ell<=m. Minimality forces ell=m.

**Corollary.** Any least counterexample to (A) produces a prime-index block all of whose prime divisors are WSS, and at least one of those divisors has odd initial depth at least three.

**Proof.** The least index ell is prime by PBC2. Each prime divisor p of F_ell has rank ell and initial depth h_p=v_p(F_ell)>=2. Hence q_p=0. The classical Fibonacci square classification excludes F_ell from the squares, so at least one exponent is odd and therefore at least three. Here ell is the index prime; no assertion that q_ell=0 follows.

PBC2 proves an equivalence and the shape of a least counterexample. It does not assert (A) or (B).

### PBC.3. All largest-prime power layers preserve exceptional depth

**Theorem.** Let m>1 have largest prime factor ell>=7, and put a=v_ell(m). For 1<=j<=a define the positive integer

$$
C_j=\frac{F_{\ell^j}}{F_{\ell^{j-1}}}.
$$

Then C_j>1, the C_j are pairwise coprime, C_j is not a square, and every prime p dividing C_j satisfies

$$
\rho(p)=\ell^j,\qquad p>\ell,\qquad
v_p(C_j)=h_p=v_p(F_m).\tag{PBC3}
$$

If F_m is powerful, every C_j is powerful, and there exist a distinct primes p_1,...,p_a such that

$$
\boxed{\rho(p_j)=\ell^j,\qquad h_{p_j}\ge3\text{ is odd},\qquad q_{p_j}=0.}\tag{PBC4}
$$

**Proof.** Fibonacci divisibility and strict growth give integral C_j>1. Every prime p dividing F_(ell^j) is different from two and five, whose ranks are three and five. Its rank divides ell^j and is greater than one, hence equals ell^i for some 1<=i<=j. The rank bound rho(p)|p-(5/p) implies p>rho(p): otherwise p=rho(p)-1 would be even and greater than two. In particular p>ell and p does not divide m. The valuation formula shows that v_p(F_(ell^j))=h_p and that this also equals v_p(F_m).

For j>=2, every old prime divisor of F_(ell^(j-1)) is different from ell. Multiplying its zero index by ell therefore leaves its valuation unchanged. It cannot divide C_j. Thus gcd(C_j,F_(ell^(j-1)))=1, which also proves pairwise coprimality of all layers. Any prime in C_j must have rank ell^j, and the asserted valuation equalities follow. The j=1 case has previous factor F_1=1.

If C_j were square, the distinct positive odd indices ell^(j-1) and ell^j would give Fibonacci numbers in the same square class. The classical square-class theorem excludes this. The theorem is stated by P. Ribenboim in *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), section 3.4, https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf ; its only nonsingleton positive-index classes are {1,2,12} and {3,6}.

Finally, powerful F_m and PBC3 force every exponent in C_j to be at least two. Since C_j is not square, some exponent is odd and at least three. Choose one such prime p_j for each layer. Distinct ranks, or pairwise coprimality, ensure these primes are distinct. No exceptional prime is supplied without the powerfulness antecedent.

### PBC.4. An exact partition dominates the zero-block sieve bound

**Definition.** For real 7<=Y<=L, let H(Y,L) count primes ell in [Y,L] with F_ell powerful. Let G(Y,L) count distinct primes ell in that interval which equal rho(p) for at least one prime p with q_p nonzero. Let Pi(Y,L) count all primes in [Y,L].

**Theorem.** For every such interval,

$$
\boxed{G(Y,L)+H(Y,L)=\operatorname{Pi}(Y,L).}\tag{PBC5}
$$

**Proof.** All prime divisors of F_ell have rank ell when ell>=7 is prime. The integer F_ell is not powerful exactly when one such divisor has exponent one. That exponent is its actual initial depth. This is equivalent to ell being the rank of a non-WSS prime. Thus the two counted classes are disjoint and exhaust the interval's prime indices.

**Proposition, comparison with ZBD3.** Retain the definitions y=X^(4/35), H(X), and R_8(X) of EMWS and ZBD. For sufficiently large X,

$$
\boxed{R_8(X)+H(X)\ge\operatorname{Pi}(y,60X+1).}\tag{PBC6}
$$

If H(X)=o(X/log X), then

$$
G(y,60X+1)\sim\frac{60X}{\log X},\tag{PBC7}
$$

and the number of non-WSS primes p<=x with prime Fibonacci rank is at least a positive constant times log(x)/log(log(x)) for all sufficiently large x.

**Proof.** A prime rank ell in [y,60X+1] is squarefree, is coprime to 60, and has one odd prime factor at least y. Thus each G rank is counted by R_8(X). Apply PBC5 to obtain PBC6. The prime number theorem gives Pi(y,60X+1) asymptotic to 60X/log X; subtract the hypothesized H bound for PBC7.

For each G rank select one supporting non-WSS prime p. Different ranks have different supporting primes, and p divides F_ell<=2^ell. Take X=floor(log(x)/(120 log 2)). Then 2^(60X+1)<=2sqrt(x)<=x for large x. PBC7 therefore supplies the stated lower bound on primes up to x.

Since the right side of PBC6 has order X/log X, this direct partition is stronger than ZBD3's lower bound of order X^(4/35)/(log X)^4. It needs no four-form sieve. It also weakens the sufficient H-smallness assumption used in ZBD.2. No bound on H is proved by this comparison; the separate EMW-based implication in EMWS.4 is unchanged.


## Appendix FDP. Exact parity frequency of the Fibonacci square-plus-one divisor count

**Definition.** Let a(n)=|D_F(F_n^2+1)| for n>=0, as in FDS. For t>=0 let

$$
O(t)=\left\lfloor\frac{\lfloor\sqrt t\rfloor+1}{2}\right\rfloor,
$$

the number of positive odd squares not exceeding t.

**Theorem.** For even n>=2, a(n) is even exactly when n-1 or n+1 is an odd square. For odd n>=3, a(n) is even exactly when n-2 or n+2 is an odd square. Moreover a(0)=1 and a(1)=2.

**Proof.** FDS5 gives a(n)=tau(u)+tau(v)-1, with the indicated u,v. Pairing complementary divisors shows that tau(t) is odd exactly when t is square. Thus a(n) is even exactly when precisely one of u,v is square. These numbers are odd, and their difference is two or four. Distinct positive odd squares differ by at least eight, so they cannot both be square. The two initial values are FDS.2.

**Theorem.** For every integer X>=3,

$$
\boxed{\#\{0\le n\le X:a(n)\text{ even}\}
=O(X-2)+O(X-1)+O(X+1)+O(X+2)-1
=2\sqrt X+O(1).}\tag{FDP1}
$$

**Proof.** The even indices are obtained from positive odd squares s by n=s+1 or n=s-1, excluding s=1 from the second family. They contribute O(X-1)+O(X+1)-1. The odd indices at least three are n=s+2 or n=s-2, excluding s=1 from the second family, contributing O(X-2)+O(X+2)-1. The index n=1 contributes one. These families are disjoint: opposite parities cannot meet, while a same-parity overlap would give odd squares differing by two or four. Summing gives the exact formula. Since O(t)=sqrt(t)/2+O(1), the asymptotic follows with a bounded error.


### FDS.4. Fibonacci-valued divisor sums at Fibonacci centres

**Definition.** For a positive integer N, retain the distinct-value divisor set D_F(N) from FDS.1 and put

$$
\sigma_F(N)=\sum_{d\in D_F(N)}d.
$$

The value one is counted once. Let \(\mathcal F_+=\{F_n:n\ge2\}\).

**Lemma.** If a finite subset S of \(\mathcal F_+\) contains one and has Fibonacci sum, then either S={1}, or for some r>=2,

$$
S=\{1,F_3,F_5,\ldots,F_{2r-1}\},\qquad \sum S=F_{2r}.
\tag{FDS10}
$$

**Proof.** This is the finite-set statement FSP2. A direct proof is as follows. The sum of F_2 through F_(n-2) is F_n-2 for n>=3. Thus an anchored set summing to F_n must contain F_(n-1), since it cannot contain F_n itself along with the additional positive term one. At n=3 such a set is impossible. For n>=4 remove F_(n-1); the remaining set still contains one and sums to F_(n-2). Induction terminates at F_2=1 and forces precisely the stated alternating shape. Conversely its sum telescopes by the recurrence. In the nonsingleton case its largest index is 2r-1.

**Theorem.** For every n>=0,

$$
\boxed{\sigma_F(F_n^2+1)\in\mathcal F_+
\quad\Longleftrightarrow\quad n\in\{0,1,2,4\}.}
\tag{FDS11}
$$

At these indices the sums are respectively 1,3,3,8.

**Proof.** For n>=2 let u,v be the two odd coprime indices from FDS4, with u<v. The divisor set contains F_v and contains no larger Fibonacci value. If its sum is Fibonacci, FDS10 forces all odd indices from 3 through v to occur.

If n is odd, then v=n+2>=5 and u=v-4. The required index v-2 is larger than u and cannot divide v, since it is an odd integer at least three and would have to divide two. This contradicts FDS4.

If n is even and n>=6, then v=n+1>=7 and u=v-2. The required index d=v-4 is an odd integer at least three. It cannot divide u=d+2 or v=d+4, since that would make it divide two or four. Again FDS4 gives a contradiction.

The remaining cases have actual divisor sets {1} at n=0, {1,2} at n=1,2, and {1,2,5} at n=4. Their sums prove sufficiency and the asserted values.

### FDS.5. Fibonacci-valued divisor sums at Lucas centres

**Lemma.** For every odd n>=1,

$$
D_F(L_n^2+1)=
\begin{cases}
\{1\},&3\mid n,\\
\{1,2\},&3\nmid n.
\end{cases}
\tag{FDS12}
$$

**Proof.** Put M=L_n^2+1. The golden identities give F_(3n)=F_n M and M+3=5F_n^2. Any common divisor of F_n and M divides three, while strong divisibility gives gcd(F_n,3)=gcd(F_n,F_4)=F_gcd(n,4)=1. Hence gcd(F_n,M)=1.

If k>=3 and F_k|M, then F_k|F_(3n), so strong divisibility and strict Fibonacci growth give k|3n. Also F_gcd(k,n)=gcd(F_k,F_n)=1. Since n is odd, gcd(k,n) is odd and must be one. Therefore k|3, so k=3 and F_k=2. Finally M+3=5F_n^2 modulo two shows 2|M exactly when F_n is odd, equivalently 3 does not divide n. This rederives the previously established odd-Lucas classification.

**Theorem.** For every n>=0,

$$
\boxed{\sigma_F(L_n^2+1)\in\mathcal F_+
\quad\Longleftrightarrow\quad n\text{ is odd}\ \text{or}\ n\in\{2,4,8\}.}
\tag{FDS13}
$$

For odd n the sum is one when 3|n and three otherwise. At n=2,4,8 the sums are respectively 8,8,55.

**Proof.** FDS12 settles all odd n. At n=0 the actual sum is 1+5=6, not Fibonacci. At n=2,4 the divisor set is {1,2,5}, giving eight. For even n>=6 set v=n+1 and u=v-2. By FDS8 the largest divisor index is v, and the allowed non-unit indices are divisors of u or v together with the additional index five. FDS10 would require the index d=v-4. This odd d>=3 divides neither u nor v, by their differences two and four. Therefore d must equal five, forcing v=9 and n=8. Conversely, at n=8 the divisor set is {1,2,5,13,34}, whose sum is 55=F_10.

FDS11 and FDS13 are consequences of the full divisor spectra and anchored-sum rigidity. They classify the two subsequences obtained by evaluating OEIS A339621 at Fibonacci and Lucas arguments.

### FDS.6. No Fibonacci divisor-sum at a minus-one Fibonacci square

**Theorem.** For every n>=3,

$$
\boxed{\sigma_F(F_n^2-1)\notin\mathcal F_+.}
\tag{FDS14}
$$

**Proof.** For odd n, Cassini gives F_n^2-1=F_(n-1)F_(n+1); for even n it gives F_n^2-1=F_(n-2)F_(n+2). In both cases the factor indices u<v are positive and even, and v>=4. FDS3 shows that the largest Fibonacci divisor is F_v and that there is no larger Fibonacci divisor. The nonsingleton anchored-set classification FDS10 requires its largest Fibonacci index to be odd if the sum is Fibonacci. This contradicts the evenness of v.

### PBC.5. Collective depths in a fully exceptional prime block

**Theorem.** For every prime ell>=7,

$$
\boxed{\gcd\{h_p:p\mid F_\ell,\ p\text{ prime}\}=1.}\tag{PBC8}
$$

Consequently a powerful F_ell has at least two distinct WSS prime divisors, and at least one has odd initial depth at least three.

**Proof.** All its prime divisors have rank ell, so F_ell=product p^h_p. A common divisor d>=2 of the exponents would make F_ell a perfect d-th power. The established perfect-power theorem of Bugeaud, Mignotte and Siksek excludes this: its only Fibonacci values are 0,1,8,144, occurring at indices 0,1,2,6,12. None occurs at a prime ell>=7. In a powerful block all h_p>=2. A singleton support would then have exponent gcd at least two; all-even exponents would have the same defect. This proves the conclusions. The theorem used is *Classical and modular approaches to exponential Diophantine equations I. Fibonacci and Lucas perfect powers*, Annals of Mathematics 163 (2006), 969-1018, DOI 10.4007/annals.2006.163.969, https://annals.math.princeton.edu/2006/163-3/p05 . It classifies perfect powers, not all powerful Fibonacci integers. Collective gcd one does not assert pairwise coprimality of the depths.

**Corollary.** For every k>=1, if F_(60k)^2-1,F_(60k)^2,F_(60k)^2+1 are powerful, at least eight distinct WSS primes occur in four distinct prime-rank blocks, including at least four primes with odd depth at least three.

**Proof.** EMW-C3 makes all four neighbouring Fibonacci terms powerful. The four positive odd numbers 60k-1,60k+1,30k-1,30k+1 are pairwise coprime and coprime to 30. Their largest prime factors are therefore four distinct primes at least seven. Apply ZBD1 to each neighbouring index, using the same largest prime for an even index and its odd half. This produces four powerful prime-index blocks. Their Fibonacci values are pairwise coprime. Apply PBC8 in each block. No sieve condition on k is needed, and the antecedent is not asserted to hold.

**Corollary.** Let N_0(x) and N_Z(x) count non-WSS and WSS primes p<=x, respectively, whose actual Fibonacci ranks are prime and at least seven. For x>=128,

$$
\boxed{N_0(x)+\tfrac12N_Z(x)\ge\pi(\lfloor\log_2x\rfloor)-3.}\tag{PBC9}
$$

**Proof.** Set Y=floor(log_2 x). Every prime ell in [7,Y] has either a simple prime divisor of F_ell or a powerful block. In the first case choose one non-WSS prime; in the second choose two WSS primes by PBC8. Distinct indices give disjoint prime supports. All chosen primes are at most F_Y<=2^Y<=x. Each index contributes at least one to the weighted left side. This strengthens the counting consequence of PBC5 but does not select the zero or nonzero alternative. No bound on the exceptional-block count follows from this inequality alone.


## Appendix LFO. Powerful residue classes and finite-prime observation at prime ranks

### LFO.1. Exact residue compatibility

**Definition.** For M>=1, let C(M) be the set of residue classes modulo M containing a positive powerful integer. The residue of an integer a is denoted [a]_M. A positive integer is powerful exactly when it has a representation x^2 y^3 with positive integers x,y: in its prime factorization, an even exponent is assigned wholly to the square, and an odd exponent at least three is assigned three to the cube and the remaining even exponent to the square.

**Theorem.** For every integer a and M>=1,

$$
\boxed{[a]_M\in C(M)\quad\Longleftrightarrow\quad
\forall p\text{ prime},\ p^2\mid M\Longrightarrow
(p\nmid a\ \lor\ p^2\mid a).}\tag{LFO1}
$$

In particular every unit residue class belongs to C(M), and every residue class does so when M is squarefree.

**Proof.** If p^2|M and p divides a exactly once, every integer in the residue class has exponent exactly one at p. This proves necessity.

For sufficiency write e_p=v_p(M) for p|M and let t_p be the largest t<=e_p for which p^t|a. Thus t_p=e_p if a is zero modulo p^e_p; no valuation of zero is taken. Choose nu_p=0 when t_p=0, nu_p=t_p when 0<t_p<e_p, and nu_p=max(e_p,2) when t_p=e_p. The hypothesis ensures that every positive nu_p is at least two. Hence D=product_{p|M}p^nu_p is powerful.

There is a unit u modulo M with Du congruent to a. At t_p<e_p, the congruence reduces to

$$
u\equiv(a/p^{t_p})(D/p^{t_p})^{-1}\pmod{p^{e_p-t_p}}.
$$

Both factors on the right are units at p; choose any unit lift modulo p^e_p. At t_p=e_p the original congruence is automatic, and choose u=1 modulo p^e_p. The Chinese remainder theorem combines these unit classes. Choose positive x,y representing u^(-1),u modulo M. Then N=Dx^2y^3 is powerful and N congruent to Du=a modulo M. When M=1 take D=x=y=1.

### LFO.2. Compatibility survives non-perfect-power and finite-support constraints

**Theorem.** Suppose [a]_M belongs to C(M). Given any integer B>=1, the class contains infinitely many positive powerful integers N which are not perfect powers and have no prime divisor p<=B with p not dividing M. At two distinct auxiliary primes r,s>B not dividing M, their exponents may be fixed to be exactly two and three, respectively.

**Proof.** Use the D and unit u from LFO1. Infinitude of primes supplies distinct r,s>B outside the prime support of M. Let R be the product of primes p<=B with p not dividing M. The moduli M,R,r^2,s^2 are pairwise coprime. The Chinese remainder theorem gives positive x,y with

$$
\begin{array}{c|cccc}
 &\bmod M&\bmod R&\bmod r^2&\bmod s^2\\
x&u^{-1}&1&r&1\\
y&u&1&1&s
\end{array}
$$

and N=Dx^2y^3 is powerful, congruent to a modulo M, and divisible by none of the stated small primes. Since r,s do not divide D, its exponents at r,s are exactly two and three. A perfect-power exponent would divide both, which is impossible. Replace x by x+jL for j>=0, where L=MRr^2s^2, to obtain infinitely many distinct examples with all conditions unchanged. Congruences modulo one are vacuous. The elementary construction does not use a theorem on primes in arithmetic progressions.

**Corollary.** Imposing the additional requirement that a powerful integer is not a perfect power does not change its image modulo any positive M.

**Proof.** The preceding theorem gives the reverse inclusion; the other inclusion is immediate. In the constructed examples the collective gcd of the prime exponents is one because exponents two and three occur.

**Proposition.** For fixed compatible a,M,B, there are constants C,T_0>0 such that every real T>=T_0 has one of these examples in [T,T+C sqrt(T)].

**Proof.** Keep D,y,L and the residue of x from the preceding proof. Put A=Dy^3. Select the first positive x_j=x+jL with x_j>=sqrt(T/A). For sufficiently large T this choice has x_j<sqrt(T/A)+L. Thus

$$
T\le Ax_j^2<T+2L\sqrt{AT}+AL^2.
$$

For T>=1 the last two terms are bounded by C sqrt(T), with C=2L sqrt(A)+AL^2. All congruence and exponent conditions remain unchanged. The constants depend on the fixed residue data; no estimate uniform in a growing modulus is asserted.

Squarefull numbers in arithmetic progressions have an extensive classical literature, including M. Munsch, I. E. Shparlinski and K. H. Yau, *Smooth squarefree and squarefull integers in arithmetic progressions*, Mathematika 66 (2020), 56-70, DOI 10.1112/mtk.12012, https://arxiv.org/abs/1810.02573 . The claims here use the explicit elementary construction rather than an unproved distribution assumption.

### LFO.3. The exact proportion of locally admissible residues

**Theorem.** For every M>=1,

$$
\boxed{\frac{|C(M)|}{M}
=\prod_{p^2\mid M}\left(1-\frac1p+\frac1{p^2}\right).}\tag{LFO2}
$$

**Proof.** At a prime power p^e with e=1 all classes are admissible. For e>=2, precisely p^(e-1)-p^(e-2) classes have valuation one. Subtract them from p^e, divide by p^e and multiply over the independent prime-power factors using the Chinese remainder theorem. Empty products equal one, including M=1.

### LFO.4. What fixed value-prime probes can see in a prime-index block

**Theorem.** Let ell>=7 be prime. Every prime divisor p of F_ell satisfies

$$
\rho(p)=\ell,\quad p\equiv1\pmod4,\quad
\begin{cases}
p\ge4\ell+1,&(5/p)=1,\\
p\ge2\ell-1,&(5/p)=-1.
\end{cases}\tag{LFO3}
$$

These are classical rank and golden-norm consequences.

**Proof.** The ranks of two and five exclude them from F_ell. The rank of any other prime divisor divides ell and is greater than one, so it equals ell. At this odd index the norm identity gives L_ell^2-5F_ell^2=-4. Modulo p, L_ell/2 is a square root of minus one, so p=1 modulo four. The rank bound gives ell|p-(5/p). For a split prime, both ell and four divide p-1, giving 4ell|p-1. For an inert prime, the positive integer (p+1)/ell is even, giving p>=2ell-1. More precisely that integer is two modulo four.

**Corollary.** Let P(M) be the largest prime factor of M, with P(1)=1. If 2ell-1>P(M), then gcd(F_ell,M)=1. Thus [F_ell]_M belongs to C(M) and contains the non-perfect powerful examples of LFO.2. Increasing the exponents on the same finite prime support does not alter this assertion.

**Proof.** A common prime divisor would contradict LFO3. Apply LFO1 and LFO.2 to the resulting unit class.

**Definition.** A residue-only rejection rule at modulus M is called sound for nonpowerfulness if it rejects a residue class only when every positive integer in that class is nonpowerful.

**Theorem.** Every such sound rule accepts F_ell whenever ell is prime, ell>=7, and 2ell-1>P(M). A finite collection of residue-only rules can be combined at their least-common-multiple modulus and has the same eventual acceptance property. In particular, on prime indices ell in [Y,2Y] with Y>=7, probes supported only on value primes below 2Y-1 reject no index.

**Proof.** The corollary provides a positive powerful integer in the same class. Rejecting it would violate soundness. Equality modulo the least common multiple preserves all the individual residues. Apply the same corollary once to that modulus.

This theorem concerns the specified residue-only information. It does not assert that every arithmetic argument involving congruences is powerless, nor does it apply to moduli whose prime support is allowed to grow past the stated cutoff. Replacing F_ell by a compatible powerful integer preserves polynomial congruences in the numerical Fibonacci/Lucas coordinates at those fixed moduli. It does not preserve the exact integer norm equation, the actual recurrence value, or exact ranks of the replacement integer's prime factors.

### LFO.5. The exact finite set of exclusions

**Theorem.** For every positive M and prime ell>=7,

$$
\boxed{[F_\ell]_M\notin C(M)
\quad\Longleftrightarrow\quad
\exists p\text{ prime}:\ p^2\mid M,\ \rho(p)=\ell,\ q_p\ne0.}\tag{LFO4}
$$

Consequently the prime indices excluded by M are exactly the distinct prime ranks at least seven of the non-WSS primes whose squares divide M. This is a finite set, contained in [7,(P(M)+1)/2].

**Proof.** By LFO1, exclusion is equivalent to p dividing F_ell exactly once for some p^2|M. Such p is different from two and five and has rank ell by LFO3; its exponent is its initial depth. EMW-B3 makes exponent one equivalent to q_p nonzero. These steps reverse to prove both implications. Finally p<=P(M) and p>=2ell-1 give the bound on ell.

**Proposition.** The integers F_7=13 and N=29^2*37^3=42599173 have the same residue four modulo nine. The latter is powerful, is not a perfect power, and its two prime divisors exceed thirteen and are both one modulo four.

**Proof.** The displayed factorizations and residues are exact integer calculations, and the exponents two and three have gcd one. The primes twenty-nine and thirty-seven do not divide F_7 and are not asserted to have rank seven. This example records the distinction between residue compatibility and membership in an actual prime-index Fibonacci block.


## Appendix GAW. Linear-index reduction for aligned prime witnesses

### GAW.1. The exact arithmetic objects and linear reduction

**Definition.** Let F_0=0,F_1=1,F_(n+2)=F_(n+1)+F_n. For a prime p, let rho(p) be its least positive Fibonacci zero index. Let pi(q) be the least positive t for which Q^t=I modulo q, where Q=((1,1),(1,0)); this is the Pisano period. For primes q>5 put epsilon_q=(5/q), N_q=q-epsilon_q, h_q=v_q(F_rho(q)) and q_q=F_(N_q)/q modulo q. An aligned prime witness for q is a prime p congruent to one modulo q with rho(p)|pi(q).

**Lemma.** For a prime q other than two and five, pi(q)|q-1 when epsilon_q=1, and pi(q)|2(q+1) when epsilon_q=-1. In particular q does not divide pi(q).

**Proof.** Over the quadratic splitting field, Q has distinct eigenvalues alpha,beta with alpha*beta=-1. In the split case both lie in F_q^*, so their orders divide q-1. In the inert case Frobenius interchanges them, giving alpha^(q+1)=beta^(q+1)=-1 and Q^(q+1)=-I. Hence Q^(2(q+1))=I. These prove the period bounds and coprimality. The same golden Frobenius argument gives rho(p)|p-epsilon_p. These are the classical prime-period and apparition bounds of Wall and Carmichael, not additional exceptional-prime assumptions.

**Theorem.** Let q>5 and p=kq+1 be primes, k>=4, and suppose r=rho(p) divides pi(q). Then

$$
\begin{array}{c|c}
(\epsilon_p,\epsilon_q)&\text{necessary index divisibility}\\
(1,1)\text{ or }(1,-1)&r\mid k\\
(-1,1)&r\mid k+2\\
(-1,-1)&r\mid2(k-2).
\end{array}\tag{GAW1}
$$

Consequently p divides at least one of F_k,F_(k+2),F_(2(k-2)).

**Proof.** If epsilon_p=1, then r|p-1=kq and gcd(r,q)=1 by the period lemma, so r|k. If epsilon_p=-1 and epsilon_q=1, subtract k(q-1) from kq+2 to obtain r|k+2. If both signs are negative, subtract 2(kq+2) from k*2(q+1) to obtain r|2(k-2). The apparition divisibility criterion and Fibonacci divisibility finish the proof. Odd k are already impossible because p would be even and greater than two.

The all-k question is OQ2 in A. Goel, *Sophie Germain Primes and the Totient of Fibonacci Numbers*, arXiv:2604.17847v3, Section 10, https://arxiv.org/html/2604.17847v3 . Its Theorem 4.2 gives a deterministic multiplier range through 31 and non-exhaustive factor-table evidence through 100. GAW1 uses the signed prime-period bounds to replace the quadratic candidate index k^2-4 by linear indices. The ramified q=5 exception is excluded in that version of the source as well.

### GAW.2. Complete exclusion for multipliers through two hundred

**Theorem.** Let q be an odd prime other than five, and let p=kq+1 be prime with 2<=k<=200. Then

$$
\boxed{\rho(p)\mid\pi(q)\quad\Longrightarrow\quad k=2.}\tag{GAW2}
$$

There is no bound on q or p.

**Proof.** For q=3, Q^8=I modulo three and F_8=21. Thus an aligned p divides 21. The conditions p=3k+1 and k>=2 leave only p=7,k=2. Now take q>5 and even 4<=k<=200. By GAW1 it suffices to enumerate every prime divisor of the three indicated Fibonacci numbers.

The complete integer factorization certificate covers the set {k,k+2,2(k-2):4<=k<=200, k even}, containing 149 different indices, all at most 396. It gives all 353 different prime divisors. For each claimed prime n>2, the certificate supplies n-1=product r^e with recursively certified smaller primes r, and an integer a satisfying

$$
a^{n-1}\equiv1\pmod n,\qquad
\gcd(a^{(n-1)/r}-1,n)=1\quad(r\mid n-1).\tag{GAW3}
$$

This is a primality proof: modulo any prime divisor t of n, the order of a is exactly n-1, hence n-1|t-1 and t>=n. Thus t=n. The recursion ends at two. The Fibonacci factorization products equal the actual recurrence values, so no cofactor is omitted. Every composite quotient (p-1)/k>5 has an explicit proper divisor; every prime quotient has the same recursive primality certificate.

After these exact tests, the only candidates are the following. Each row satisfies Q^t=I modulo q and the displayed nonzero residue F_t modulo p.

| k | p | q | t | F_t mod p |
|---:|---:|---:|---:|---:|
|54|5779|107|72|2584|
|70|911|13|28|783|
|78|859|11|10|55|
|118|336419|2851|2850|2584|
|160|3041|19|18|2584|
|162|3079|19|18|2584|
|164|2789|17|36|835|
|174|947104099|5443127|10886256|866005836|
|194|3299|17|36|2377|
|198|2179|11|10|55|

These are integer congruences. Since pi(q)|t, any alignment rho(p)|pi(q) would force p|F_t, contradicting the last column. There is no need to prove t is the least period. This excludes every candidate and proves GAW2.

The mathematical data for the finite proof are the complete product, primality and proper-divisor certificates retained at `Evidence/D5/S3/Arith/GoelAlignedWitness200/certificate.json`; its decoded JSON has SHA-256 `0373b90e7386142c3afd0bab7d1272ec9a1a9987321b187a1695de267f910318`. The proof uses the arithmetic identities in the certificate, not an assumption that probable-prime tests succeed. GAW2 is a bounded-multiplier theorem and does not assert the all-k conclusion of OQ2.

**Boundary proposition.** The q=5 exclusion in GAW2 is necessary.

**Proof.** The known ramified example p=41=8*5+1 has rho(41)=20=pi(5). The zero at twenty and the absence of zeros at its proper divisors are exact Fibonacci computations. This is the exception already stated in the source, rather than a new refutation.

### GAW.3. The zero residue of the totient problem retains the actual WSS branch

**Definition.** For a prime q>5 and P=pi(q), let S(q) be the set of residues a modulo P such that q divides Euler's totient tot(F_m) for every positive integer m congruent to a modulo P. Only positive indices are used, so tot(F_0) is never invoked.

**Theorem.** With h_q and q_q as in GAW.1,

$$
\boxed{
v_q(\operatorname{tot}(F_P))
=h_q-1+\sum_{\substack{p\mid F_P\ p\ne q\ p\text{ prime}}}v_q(p-1).
}\tag{GAW4}
$$

Consequently

$$
\boxed{
0\in S(q)\iff q\mid\operatorname{tot}(F_P)
\iff q_q=0\ \text{or}\ \exists p\text{ aligned for }q.
}\tag{GAW5}
$$

**Proof.** Since rho(q)|P and q does not divide P, the classical Fibonacci valuation formula gives v_q(F_P)=h_q. In tot(F_P)=product p^(v_p(F_P)-1)(p-1), the contribution of p=q is h_q-1. Every other prime p contributes only v_q(p-1). This proves GAW4. If q divides tot(F_P), then it divides tot(F_(uP)) for every u>=1: F_P divides F_(uP), and A|B for positive integers implies tot(A)|tot(B), directly from prime factorization. The reverse implication takes u=1. Nonnegativity in GAW4, the actual WSS criterion h_q>=2 iff q_q=0, and p|F_P iff rho(p)|P prove GAW5.

**Corollary.** For every prime q>5,

$$
\boxed{0\in S(q)\iff q_q=0\ \text{or}\
\bigl(2q+1\text{ prime and }\rho(2q+1)\mid\pi(q)\bigr)\ \text{or}\
\exists p>200q+1:\ p\text{ prime},\ p\equiv1\pmod q,\ \rho(p)\mid\pi(q).}\tag{GAW6}
$$

**Proof.** Every aligned prime has p=kq+1 for an even k>=2. GAW2 leaves k=2 or k>200. Apply GAW5. Every branch conversely supplies the required totient divisibility.

**Theorem.** Suppose a is a residue in S(q). If rho(q) does not divide a, every positive m congruent to a modulo P has a prime divisor p of F_m with p congruent to one modulo q. If rho(q)|a and h_q=1, at least a fraction (q-1)/q of that progression, measured by its progression parameter, necessarily has such a prime divisor. If rho(q)|a and h_q>=2, then a belongs to S(q) without requiring any such other-prime witness.

**Proof.** In the first case q never divides F_m, so Euler's product forces a different prime p with q|p-1. In the second case v_q(F_m)=1+v_q(m/rho(q)). Because q is coprime to P/rho(q), exactly one progression-parameter class modulo q makes q divide m/rho(q). In the other q-1 classes the q-primary contribution to the totient is zero, so an external witness is forced. In the third case v_q(F_m)>=2 at every such index, and the q-primary factor alone gives the totient divisibility.

The second conclusion is a positive-proportion assertion; it does not say that all but finitely many progression members lack the q^2 contribution. The proof never infers h_q=1 from a finite search for WSS primes. In particular GAW4-GAW6 retain the branch left unproved by that inference in Lemma 4.3 of the cited preprint. None of these identities proves that the WSS branch or the large-witness branch occurs, and none supplies an upper bound for the prime-index powerful-block count H_*(Y).

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
## TR. 环面返回模、有限观察与粘合信息

### TR.1 对象与研究目标

本节延续周期树的整数矩阵、同余与观察者研究。固定列向量约定，对整数二阶矩阵 A 定义真实返回模

$$R(A,n)=\mathbb Z^2/(A^n-I)\mathbb Z^2.$$

这里使用像子模的商，基数随后由格指数定理推得。不能把行列式的绝对值定义成“周期点数”，再声称已经识别实际周期点。环面自同构固定点与返回模之间的拓扑对应、映射环面的基本群及一阶同调，属于需要另行构造和证明的接口。

既有 `MinimalBinaryUnimodularBreak` 给出 Fibonacci 矩阵及其平方的实际谱资料。本节在同一整数二阶矩阵类别中研究一个可完全计算的校准族。该族的判别式为 16k(k+1)，k=1 时对应 Q(sqrt(2))，不能与原黄金域 Q(sqrt(5)) 混同。

源稿状态：本节 TR.2–TR.4 给出完整普通数学证明及对应 Lean 证明脚本；本轮没有执行 Lean 内核或 Scribe 编译。有限整数诊断只检查实现，不替代全称证明。这里不主张发现了新的三维流形分类定理，不计入开放问题解决数。

### TR.2 无界等谱族

对任意自然数 k，定义

$$C_k=\begin{pmatrix}4k+1&1\\4k&1\end{pmatrix},\qquad
D_k=\begin{pmatrix}2k+1&2\\2k(k+1)&2k+1\end{pmatrix},\qquad
P_k=\begin{pmatrix}1&0\\-2k&2\end{pmatrix}.$$

二者行列式均为 1，迹均为 4k+2。直接乘法给出 C_k P_k=P_k D_k，且 det(P_k)=2。由归纳，对每个 n≥0 有

$$(C_k^n-I)P_k=P_k(D_k^n-I).$$

取行列式并在整数中约去非零的 2，得到全部时间的带符号恒等式

$$\det(C_k^n-I)=\det(D_k^n-I).$$

P_k 是度数为 2 的整数同源映射，不能当成整数基变换。该区别是以下障碍的来源。

Lean：`D5/S3/Observer/Dynamics/ToralReturnModuleSpectrum.same_return_determinant`。

### TR.3 从实际商对象得到基数

令 k>0、n>0。C_k 的各项非负；归纳证明 C_k^m 的两个对角元至少为 1。对 n=m+1，右乘 C_k 后的迹为

$$(4k+1)(C_k^m)_{00}+4k(C_k^m)_{01}+(C_k^m)_{10}+(C_k^m)_{11}>2.$$

又因 det(C_k^n)=1，二阶恒等式给出

$$\det(C_k^n-I)=2-\operatorname{tr}(C_k^n)<0.$$

因此两个返回矩阵都非奇异。对任意非奇异整数二阶矩阵 M，M 在 Z² 上的作用是单射，因而给出 Z² 到其像子模的加法同构。将这一实际同构代入 mathlib 的 `Submodule.natAbs_det_equiv`，得到

$$\#(\mathbb Z^2/M\mathbb Z^2)=|\det M|.$$

所以，对全部正 k、正 n，R(C_k,n) 与 R(D_k,n) 都有相同的正有限基数。n=0 的商是无限的 Z²，不纳入这个有限基数结论。

Lean：`equal_cardinality_return_modules`。这一步消费实际商的构造，未将有限性、基数公式或目标等式作为独立输入假设。

### TR.4 全部整数交织子的偶性障碍

令 U=[[a,b],[c,d]] 为任意整数矩阵。如果 C_k U=U D_k，则第一行的两个方程强制

$$c=2k((k+1)b-a),\qquad d=2(a-kb).$$

因此

$$\det U=2\bigl[a(a-kb)-kb((k+1)b-a)\bigr]$$

一定为偶数。特别地，不存在行列式为 ±1 的整数交织子。这个结论覆盖任意整数 U、任意 k，包括 k=0；与 TR.3 联立时取 k>0。

结论：完整的正时间返回商基数序列，无法确定这个类别中的整数共轭类。增加观测时间不会消除此处的信息损失；需要增加观测的结构类型。

Lean：`intertwiner_determinant_even`、`spectrum_does_not_determine_integral_conjugacy`。此处尚未将整数非共轭自动提升为未构造的三维流形不同胚。

### TR.5 从等谱障碍继续推导的精确目标

下一项应直接计算同一个 R(A,1) 的群结构，而非引入与矩阵没有证明关系的抽象群。候选坐标为

$$\pi_C(x,y)=y\pmod{4k},$$

$$\pi_D(x,y)=\bigl(x\pmod2,\; y-kx\pmod{2k}\bigr).$$

需证明每个映射满射且其核分别恰为 (C_k-I)Z²、(D_k-I)Z²。这样才能从第一同构定理得到循环群与乘积群的分类，并通过实际商上的湮灭子区别二者。更强的后续目标是在任意有限模数上给出共轭的准确判据，并保留矩阵诱导的返回作用。

这些目标属于经典 Bowen–Franks 理论内的完整可核验实例。研究价值在于刻画具体观察丢失了什么，并提供最少结构性修复；并不把“有无限数据”当成“足够识别”的替代条件。

### TR.6 文献边界与外部问题

[TR1] P. Martins Rodrigues; J. Sousa Ramos. *Bowen-Franks groups as conjugacy invariants for T^n automorphisms*. arXiv:math/0303185 (2003). https://arxiv.org/abs/math/0303185 。广义 BF 群及拓扑共轭背景；本节采用列向量，与原文行向量约定区分。

[TR2] L. F. Bakker; P. Martins Rodrigues. *Generalized Bowen-Franks Groups and Profinite Conjugacy for Hyperbolic Toral Automorphisms*. arXiv:2207.00922v1 (2022). https://arxiv.org/abs/2207.00922 。论文已给出 principal BF R-modules 对相似双曲环面自同构 profinite 共轭的完整性结论。不能将它重列为未解问题，也不能把 R-module 改为基数或无标记阿贝尔群后沿用结论。

[TR3] X. Xu. *Profinite almost rigidity in 3-manifolds*. Advances in Mathematics 480 (2025), 110505; arXiv:2410.16002v4. https://arxiv.org/abs/2410.16002 。研究 profinite completion 对紧致可定向、空或环面边界三维流形的有限歧义识别。该结果与本节的标量返回序列不是相同数据。

[TR4] X. Xu. *Profinite rigidity in lattices of PSL(2,C)*. arXiv:2608.07350v1，2026-08-07. https://arxiv.org/abs/2608.07350 。本轮新检索到的预印本摘要声称证明全部 PSL(2,C) 格在该类别内的 profinite 刚性。尚未取得全文审阅或独立认可证据，故不把它当作已核定的 Lean 依赖；但足以阻止沿用旧文献中“该一般猜想尚无人提出证明”的口径。

[TR5] A. Klukowski. *Congruence Subgroup Property for nilpotent groups and subsurface subgroups of Mapping Class Groups*. arXiv:2411.06867v2 (2024)，Conjectures 1、13，Definition 3、Lemma 14. https://arxiv.org/html/2411.06867v2 。外部目标是高亏格映射类群 CSP，以及其简单闭曲线轨道的合同子群控制：给定有限指数 Gamma 与曲线 alpha，构造合同子群 Delta 使 Delta.alpha 包含于 Gamma.alpha。检索未发现该全称轨道结论已解决的来源；此为有界检索结论，不是穷尽优先权证明。本节的环面线性实例不属于亏格至少 3 的证明，也没有闭合这个猜想。

面向该外部目标，后续必须保留真实群作用、有限特征商与曲线轨道。仅靠二维阿贝尔化、相同迹、相同返回计数都没有足够信息。可先形式化 TR5 的已知组合引理作为真实消费者的基础，再推进明确受限的曲线轨道分离情形。若仅完成线性校准，应据实报告其范围，不把它计作 CSP 或庞加莱定理的解决。


### TR.7 实际返回群的结构恢复

TR.5 的核与满射目标现有对应 Lean 证明脚本，位于 `ToralReturnModuleStructure.lean`，并配套同名 Scribe。原返回模定义直接复用，不更换载体。

对任意 k≥0，pi_C 满射，其核等于 (C_k-I)Z²。若 y=4ka，则 (a,x-4ka) 是 (x,y) 的原像。pi_D 同样满射；给定两个剩余类的整数代表 a,b，可取 (a,b+ka)。若 (x,y) 位于 pi_D 的核，写 x=2a、y-kx=2kb，则 (b,a-kb) 是其在 D_k-I 下的原像。这同时证明两项像与核的双向包含。

第一同构定理因此在同一个实际商上给出

$$R(C_k,1)\cong\mathbb Z/(4k),\qquad
R(D_k,1)\cong\mathbb Z/2\times\mathbb Z/(2k).$$

k=0 也纳入分类：按 ZMod 0=Z 的约定，左边对应 Z，右边对应 Z/2×Z。有限性及以下分离结论取 k>0。

第二个商的每个元素都被 2k 湮灭。第一个商中，将剩余类 1 经构造出的同构逆像拉回，得到不被 2k 湮灭的实际商元素；否则 4k 整除 2k，与正 k 矛盾。于是不存在两个返回商之间的加法同构。

联合 TR.3，得到无界参数、全部正时间的结论：两个系统的所有返回模基数相同，单个时间的群结构却已足够区分这两个备选。这里的附加信息是同一个原对象上的湮灭性质，未定义人为标签或外加分类分数。

主要声明：`companion_image_eq_kernel`、`balanced_image_eq_kernel`、`one_step_return_module_classification`、`balanced_return_annihilated`、`companion_return_not_annihilated`、`one_step_return_modules_not_isomorphic`、`scalar_spectrum_and_structural_separation`。

本组继续停留在普通证明与候选 Lean 源码层，未宣称已执行内核。该结构恢复是指定校准族的完整分类，不推广为任意环面自同构的单步分类。矩阵 P_k 的行列式提示下一项可证明的问题：在所有模数中，2 是否是唯一检测这一共轭差异的素数？应在实际 ZMod 作用上构造可逆交织子，并证明偶数模数的精确障碍。

### TR.8 完整交织子范数与精确模数判据

TR.7 提出的素数定位现在有全称证明脚本 `ToralReturnPrimeTwoCriterion.lean` 及对应 Scribe。系数从原整数矩阵经标准环同态输运，未引入一个只在名称上对应原系统的新模型。

对任意交换环 R、自然数 k，所有满足 C_k U=U D_k 的矩阵都恰好具有形式

$$U(a,b)=\begin{pmatrix}a&b\\2k((k+1)b-a)&2(a-kb)\end{pmatrix},\qquad a,b\in R.$$

证明的正向来自两个第一行方程；反向将该表达式代入四个矩阵元即可。推导不除以 2，因此在特征 2 中也成立。随即有精确恒等式

$$\det U(a,b)=2\bigl(a^2-k(k+1)b^2\bigr).$$

该公式把偶性障碍提升为二次范数说明。整数情形，非零交织子的格指数受这个范数控制；a=1、b=0 实现行列式 2。这里的“非零”应精确理解为行列式非零，单纯非零矩阵仍可能奇异。对应二次域随 k 变化，k=1 给出 Q(sqrt(2))。

在 ZMod(m) 上，用存在 P,Q 满足 PQ=QP=I 且 C_k P=P D_k 定义实际可逆矩阵共轭。对所有 k,m≥0：

$$C_k\text{ 与 }D_k\text{ 在 }\mathbb Z/m\text{ 上共轭}\quad\Longleftrightarrow\quad m\text{ 为奇数}.$$

充分性：写 m=2r+1，令 u=-r mod m，则 2u=1。取

$$P=\begin{pmatrix}1&0\\-2k&2\end{pmatrix},\qquad
Q=\begin{pmatrix}1&0\\k&u\end{pmatrix}.$$

直接乘法证明 PQ=QP=I 及 C_kP=PD_k。

必要性：若 2 整除 m，标准环同态 ZMod(m)→ZMod(2) 存在。任何假设的可逆交织子都必须满足 det(P)det(Q)=1。将范数公式代入再通过该同态，左侧为 0，右侧为 1，矛盾。m=0 对应整数环，亦在排除范围；m=1 为零环，满足奇数侧结论。

主要声明：`intertwiner_normal_form`、`intertwiner_quadratic_norm`、`modular_conjugacy_iff_odd`。

本族的结论非常具体：所有正时间返回商基数相同；一步返回群结构已可区分；所有奇数模数的可逆线性观察仍等价；模 2 足以检测差异。无须增加时间长度，也无须提高奇素数精度。该结论只针对已定义的族，并不推广为一般局部到整体共轭判定。

### TR.9 此后真正需要闭合的对象接口

源稿继续维持“普通数学证明及候选 Lean 脚本，未执行内核或 Scribe 编译”的层级。三个阶段实际进行了符号恒等式、整数 Smith 数据、有限模矩阵与显式逆矩阵的诊断；有限诊断不替代文件中全部参数的证明。

下一个优先任务是建立实际环面固定点与原返回模的对应。设 M=A^n-I 在实向量空间可逆，固定点群是 M^{-1}Z²/Z²。其候选同构为

$$[x]\longmapsto[Mx]\quad\text{从}\quad M^{-1}\mathbb Z^2/\mathbb Z^2\quad\text{到}\quad\mathbb Z^2/M\mathbb Z^2.$$

要完成该桥，须在真实商拓扑或 AddCircle² 状态空间上构造 A 的作用，证明固定点对象正好是左侧群，证明同构良定义、满射、单射，最后消费本节已有基数和结构定理。该对应属于经典数学，不能作为新的开放问题解决；但它是把本轮算术结果称作环面周期点结果前不可跳过的一步。

随后可以保留返回自同构及覆盖层间的作用，研究具有真正 R-module 标记的广义 BF 系统。TR2 已有的完备性定理应作为复用目标，其作用域和相似性前提必须保留。对实际三维映射环面，还需先构造基本群与同调接口，不能从某个整数矩阵的非共轭直接跳到一般三维几何结论。

外部未闭合方向维持 TR5 的高亏格映射类群 CSP 与曲线轨道合同控制。今后若尝试具体受限情形，必须增加非阿贝尔基本群的有限特征商、真实曲线轨道及已知 CSP 组合定理。这里已经证明的二维线性例子用于测量观察数据的不足及修复，尚未构成该高亏格猜想的一个证明步骤。研究推进应以能实际消费的定理依赖为依据，不以共同名称或主题相似性计数。


### TR.10 实际环面固定点与返回商的同构

本节继续同一 PR，读取的 dev 为 f8af3f0e43fce8d5cdba1e72d2cbe0cffda120d4。新增 `ToralFixedPointCokernel.lean` 与同名 Scribe。以下具有完整普通数学证明及候选 Lean 证明脚本，本轮未执行 Lean 内核或 Scribe 编译，不能从依赖的源码存在推断其已获本轮机器认证。

取 V=R²，令 j:Z²→V 为逐坐标的整数实嵌入，L=im(j)。实际状态空间为 T=V/L，使用商拓扑。整数矩阵 A 的实作用满足 A_R j(z)=j(Az)，因而保持 L；通过 Submodule.mapQ 得到实际商作用 f_A。商映射判据证明 f_A 连续，矩阵乘法与商映射复合相容，归纳得到 f_(A^n)=f_A^n。

定义 K(A,n)=ker(f_(A^n-I))。源码证明

$$z\in K(A,n)\quad\Longleftrightarrow\quad f_A^n(z)=z.$$

这里统计的是周期整除 n 的点，包括最小周期更小的点，不能将其误称为最小周期恰为 n 的点。当前结论只需要连续商作用；没有借此宣称已构造整个光滑流形或全部同胚分类接口。

设 M=A^n-I 且 det(M)≠0。用实际二阶伴随矩阵除以实行列式构造 M_R^{-1}，证明两侧逆关系。定义

$$b_M:\mathbb Z^2\longrightarrow\ker f_M,\qquad z\longmapsto[M_R^{-1}j(z)].$$

若 [x]∈ker f_M，则 M_R x∈L，故存在 z 使 M_R x=j(z)，从而 b_M(z)=[x]，证明满射。另一方面，b_M(z)=0 当且仅当 M_R^{-1}j(z) 是整数嵌入 j(w)，当且仅当 z=Mw。因此 ker(b_M)=im(M:Z²→Z²)。由第一同构定理得到

$$R(A,n)\simeq K(A,n).$$

其逆即 TR.9 提出的 [x]↦[Mx]。所有对象和映射均由原矩阵与真实实商构造；没有另给“固定点基数等于行列式”的前提。一般桥保留 det(M)≠0 的必要条件；代入原 C_k,D_k 时，正 k、正 n 的非零性直接由前驱的迹界消去。

于是 `equal_actual_periodic_cardinalities` 把 TR.3 的全部正时间基数结论提升到真实环面固定点群；`actual_fixed_groups_not_isomorphic` 把 TR.7 的一步加法群区别传到同一环面上。没有把这种固定点群非同构升级成尚未构造的映射环面奇异同调或三维不同胚定理。

主要声明：`torusAction_continuous`、`torusAction_pow_apply`、`mem_periodicGroup_iff`、`integerToTorusKernel_ker`、`returnModuleEquivPeriodicGroup`、`equal_actual_periodic_cardinalities`、`actual_fixed_groups_not_isomorphic`。同构是实际加法/整数线性同构；本节没有声称额外构造了 Homeomorph。

### TR.11 NS 连接必须保存的对象

NS 在空间环面上演化的是速度场。环面上的一个整数自同构、光滑速度的粒子流以及速度场本身的时间更新，是三种不同映射。仅有 C_k P_k=P_k D_k 不能推出任意一种 NS 方程交织。

一个额外的普通拓扑检验如下，尚未提交相应 Lean：若光滑、全局定义、随时间变化的速度场在固定环面上产生粒子流 Phi_t，t∈[0,T]，则 Phi_0=id，t↦Phi_t 给出到恒等映射的同痕，故 Phi_T 在一阶同调上作用为恒等。双曲整数环面自同构的同调作用是非恒等矩阵 A，因而不能直接等于这种同一固定环面上的粒子时间 T 映射。该论证不排除高维悬挂的截面返回映射、带孔或移动区域，也不把任意弱解自动视为光滑粒子流。

对黎曼几何版本的 NS，还需明确度量、黏性算子、压力消去和边界条件。本文选择常系数平坦度量，Christoffel 符号为零；零压力时只需实际坐标导数与逆度量 h^{ab}。这避免了曲率背景下不同向量 Laplacian 的选择问题。[TR7]

### TR.12 从原格同源得到一个真实 NS 解、障碍与修复

新增 `D5/S3/FluidDynamics/Fourier/ToralIsogenyShearNS.lean` 及对应 Scribe。它复用原 `bridge k`，并联读现役 `ReversalWaveSynthesis`、`AugmentedReadoutRecovery`。后者已完成的瞬时幅度恢复没有重复包装成本轮成果。新文件直接定义普通 deriv、混合二阶导数、散度及完整对流扩散残差；没有把 Fourier 乘子表或 PDE 解条件作为输入。

空间使用 2pi 周期。整数矩阵依然保持该周期格，但不能将它与前节周期一的坐标不加缩放地混用黏性常数。令 nu>0，取基础无外力、零压力剪切

$$u(t,X,Y)=(e^{-\nu t}\cos Y,0).$$

直接求导给出 div(u)=0、(u·grad)u=0、partial_t u=nu Delta u。原矩阵和实切向逆为

$$P_k=\begin{pmatrix}1&0\\-2k&2\end{pmatrix},\qquad
Q_k=P_k^{-1}=\begin{pmatrix}1&0\\k&1/2\end{pmatrix}.$$

向量场的实际拉回为 v(t,x,y)=Q_k u(t,P_k(x,y))，源码证明它等于

$$v(t,x,y)=(1,k)e^{-\nu t}\cos(-2kx+2y).$$

P_k 在环面上是有限覆盖，Q_k 在此作用于实切向量，不能被解释为环面上的全局逆映射，也没有建立任意速度场空间间的双射。

同步拉回度量 G_k=P_k^T P_k，逆度量为

$$H_k=Q_kQ_k^T=\begin{pmatrix}1&k\\k&k^2+1/4\end{pmatrix}.$$

源码证明所有两侧逆矩阵关系；正性由

$$(r,s)H_k(r,s)^T=(r+ks)^2+s^2/4>0\quad((r,s)\ne(0,0))$$

直接给出。对任意实 rate 和逆度量系数 h00,h01,h11，定义实际时空函数

$$v_{\lambda}(t,x,y)=(1,k)e^{-\nu\lambda t}\cos(-2kx+2y).$$

联合光滑性与两个方向的 2pi 周期性均有证明脚本。令 ell=(-2k,2)、a=(1,k)，则 ell·a=0，所以散度与两项完整非线性对流严格消失。普通导数进一步给出

$$\mathcal R_H(v_\lambda)
=\partial_t v_\lambda+(v_\lambda\cdot\nabla)v_\lambda
 -\nu(h00\partial_{xx}+2h01\partial_{xy}+h11\partial_{yy})v_\lambda
=\nu(4h00k^2-8h01k+4h11-\lambda)v_\lambda.$$

三个结论同时来自这一普通导数恒等式：

1. 保留 lambda=1，使用实际 H_k，残差为零。这是 `pulled_metric_solution`。
2. 保留同一被拉回的 v，却使用欧氏逆度量 I，得到 `pulled_euclidean_defect`：

$$\mathcal R_I(v)=\nu(4k^2+3)v.$$

在 t=x=y=0 的首分量，残差为 nu(4k²+3)>0；该不等式由 `pulled_euclidean_defect_positive` 对任意 k 和正 nu 证明。

3. 保留欧氏度量，将速率改为 lambda=4(k²+1)，得到另一个准确无外力 NS 解

$$w(t,x,y)=(1,k)e^{-4\nu(k^2+1)t}\cos(-2kx+2y).$$

`euclidean_shear_solution` 与 `euclidean_and_pulled_same_initial` 证明其方程及 w(0)=v(0)。两个演化属于不同度量方程，不能将同初值不同演化误报为同一 NS 方程不唯一。

单个剪切模式只约束 ell^T H ell=1，不唯一确定整个正定 H。上述结果证明一个规范的度量修复及原欧氏度量的失败，没有证明只有 H_k 才允许该模式。

这给出本项目的严格连接：原算术桥确实作用于一个真实 NS 剪切解；方程输运必须同时处理向量与度量。仅保留周期拓扑和矩阵交织不足以保持欧氏黏性演化。该结论是完整可计算族上的构造与诊断，使用经典几何协变机制，不主张新的 NS 存在性或正则性发现。

### TR.13 精确输运之后的分析障碍与下一项定理

新的剪切族具有特殊的非线性消去，不能据此推断一般扰动稳定，更不能从二维周期恒等式得到一般三维正则性或爆破结论。原有 NS 理论文档 `NS_OBSERVER_DYNAMICS_RH_THEORY.md` 的全模式/低模式区别依然适用；实际非共线扰动会恢复卷积、压力与导数损失。

本轮恒等式还推出一个普通数学的非一致性结论，暂未提交 Lean：H_k 的最小特征值没有对全部 k 的统一正下界。取 (r,s)=(-k,1)，上式等于 1/4，而欧氏长度平方为 k²+1，所以

$$\lambda_{\min}(H_k)\leq\frac1{4(k^2+1)}\longrightarrow0.$$

因此，即使每个 k 的变度量方程都有精确对应，也不能隐去依赖 k 的范数比较常数。这直接限制“跨所有分辨率得到统一控制”的推理。

下一项优先目标是在真实有限 Fourier 族上，给出完整的常度量 NS 输运公式，明确变换后的频率 P^T ell、向量 Q a、Leray 投影、双线性卷积及保持的频率子格。由于 P 的行列式为 2，其转置像是指数 2 的子格；任意频率截断并不自动在该变换下保持。需要给出相容截断，随后证明常数依赖 P、P^{-1}、波数截止与背景范数的稳定界。有限截断闭合之后，只有具有真实一致估计和极限识别，才能继续传递到 PDE。

另一个独立分支是噪声环面映射的输运耗散。Fannjiang-Wolowski 已把噪声扰动下的耗散时间与算术优化、环面映射的熵联系起来。[TR6] 其对象是离散映射加噪声，不是本文证明了一个光滑 NS 粒子时间映射。可复用其真实模型作为输运-扩散研究入口，不把已有渐近结果重新标记为开放问题。

外部开放目标仍需逐项确认当前版本与实际定理依赖。本文新增结果未解决高亏格 CSP，也未解决一般三维 NS 问题；未新增开放问题解决计数。关于带外力与无外力、平坦与曲率背景、强解与弱解的结论不得相互替代。后续价值应落在可被原问题消费的非线性估计、识别与一致极限上。

### TR.14 本轮来源和核验范围

[TR6] A. Fannjiang; L. Wolowski. *Noise induced dissipation in Lebesgue-measure preserving maps on d-dimensional torus*. arXiv:math/0209231v3，2003-05-07. https://arxiv.org/abs/math/0209231 。本轮核读原始摘要及可访问正文；PDF 图像工具未成功，未声称完成图像核验。只用于噪声映射/输运扩散的研究定位，不作为上述剪切恒等式的证明或新颖性来源。

[TR7] M. Arnaudon; A. B. Cruzeiro; S. Fang. *Generalized stochastic Lagrangian paths for the Navier-Stokes equation*. arXiv:1509.03491v2，2016-02-23. https://arxiv.org/abs/1509.03491 。该文明确以 Ebin-Marsden Laplacian 讨论紧黎曼流形上的 NS 与随机拉格朗日路径。本文仅使用其度量/算子选择背景，不声称形式化了随机流或一般曲率算子。

[TR2] 的 principal BF R-module 结论在本轮重新核对原始摘要，其“similar hyperbolic”和“R-module”限定均保留。固定点与格商之间的经典同构由本轮实际构造证明，没有将该文的更强完整性结论作为未注明前提。

本轮实际执行的有限诊断：2160 项有理数逆提升/格平移检验；28 个完整有理环面网格共 41280 个候选点，独立检查实际固定点计数及一步湮灭性质；32 项直接对指数三角函数求导的符号恒等式；101 个参数的逆度量/波矢诊断。另做新 Scribe 词法括号检查与源码占位扫描。这些是有限计算或符号代数核查，均不替代 Lean 内核、Scribe 编译或独立评审。暂存诊断脚本和 JSON 不提交。完成文件逐次写回同一 PR，理论只追加本节及 TR.10–TR.13。

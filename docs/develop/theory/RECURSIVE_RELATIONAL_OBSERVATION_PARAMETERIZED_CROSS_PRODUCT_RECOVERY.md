# 递归关系观察：参数化叉积原树的预测、符号损失与制备恢复

本卷在同一套非空有序二标签树上，分别研究完整数值未来、对所有制备成立的符号行为，以及原始叶对的恢复。树的原生替换始终保持所供制备；参数变化只用于解释运输。三种目标所需的记录、观察权限和恢复条件不同。

这里给出普通数学证明与有限精确核验，不提供新的 Lean 形式化，也不将散文证明或有限计算称为内核验证。经典叉积恒等式、单位方向标签、组成计数、数量反演及一般纤维判据均为复用工具。正文中的恢复是声明来源、读口和更新合同下的数学恢复，不包含物理制备、有限位传感或新的原生控制权限。

## 1. 原树、额外制备与一条实际历史

**定义 1.1（非空有序来源与原生替换）。** 来源集合 $\mathcal T$ 由有限语法

$$
t::=\alpha\mid\beta\mid\langle s,t\rangle
$$

生成。左右次序、每层括号和两种叶标签都属于来源身份；不施加交换律、结合律，也没有空树。固定

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

记实际叶数组成为 $\nu(t)=(m,n)\in\mathbb N^2$，满足 $m+n\ge1$，两个叶的组成为 $(1,0),(0,1)$，节点组成相加。复用 [Atomic §3](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的

$$
\nu(\rho t)=M\nu(t),\qquad M(m,n)=(n,m+n),\qquad M^2=M+I.
$$

**定义 1.2（参数化结构解释）。** 主载体为定向欧氏空间 $V=\mathbb R^3$，二元运算为原定向叉积。制备 $p=(a,b)\in\mathcal P=V^2$ 是额外供应的实向量数据。同一棵树中每个 $\alpha$ 都取同一个 $a$，每个 $\beta$ 都取同一个 $b$；不允许给每次叶出现独立赋值。结构解释唯一地满足

$$
E_p(\alpha)=a,\quad E_p(\beta)=b,\quad
E_p(\langle s,t\rangle)=E_p(s)\times E_p(t).
$$

实际增广来源为 $\mathcal J=\mathcal T\times\mathcal P$，实际源更新为

$$
S(t,p)=(\rho t,p),\qquad x_j(t,p)=E_p(\rho^jt)\quad(j\ge0).
$$

这直接使用 [Atomic §2](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的唯一结构延拓，没有改变原构造。

**约定 1.3（付费数值观察）。** 基本取得合同只供应一棵未知当前树及其固定未知制备。Read 返回当前精确向量、不改源；一次 $\rho$ 覆盖唯一当前源。读调用、实际更新、回复宽度、保留记录、程序、运算、精度及时间／动作／Stop 身份分别计费。初始化不供应树码、组成、叶对或校准。数量读、树码读、额外制备记录及同制备配对权限仅在明确增加它们的章节使用。确定协议只依公共合同和已取得记录选择下一事件，须在其声明域内有限停止；数值下界不使用时间或源大小侧信道。

数学解码、静态上下文和解释运输均不授予源的逆更新、复制、复位、归一化、旋转、重制备、叶重命名或任意外部向量输入。两个 live 句柄的 graft 另须有实际共同制备及权限；单个句柄的 $\rho$ 数值协议无需 graft。

## 2. 经典代数与二生成切面

**约定 2.1（Gram 数据与五个向量）。** 对任意制备置

$$
\begin{gathered}
A=|a|^2,\quad B=|b|^2,\quad C=a\cdot b,\quad
\Delta=AB-C^2,\\
K=b\times a,\qquad L=K\times a=Ca-Ab,\qquad
N=K\times b=Ba-Cb,\qquad F(a,b)=(b,K).
\end{gathered}
$$

$F$ 是解释参数的数学映射，不是实际源菜单中的动作。$\Delta>0$ 恰表示 $a,b$ 线性独立。

**引理 2.2（重复向量恒等式与切面）。** 所用叉积满足

$$
\langle u\times v,w\rangle=\langle u,v\times w\rangle,\qquad
|u\times v|^2=|u|^2|v|^2-\langle u,v\rangle^2,
$$

并有

$$
u\times(v\times u)=|u|^2v-\langle u,v\rangle u.
$$

因此 $K\perp a,b$、$|K|^2=\Delta$，约定2.1的 $L,N$ 公式成立。若 $\Delta>0$，$U_p=\operatorname{span}\{a,b,K\}$ 是闭合三维叉积切面；若 $\Delta=0$，叶生成空间至多一维，内部叉积全为零。

证明。极化范数式得

$$
\langle u\times v,u\times w\rangle
=|u|^2\langle v,w\rangle-\langle u,v\rangle\langle u,w\rangle.
$$

对任意 $z$，循环配对及此式给

$$
\langle u\times(v\times u),z\rangle
=\langle z\times u,v\times u\rangle
=|u|^2\langle z,v\rangle-\langle u,z\rangle\langle u,v\rangle.
$$

内积非退化给恒等式。垂直性来自交替性与循环配对；范数式给 $|K|^2$。于是 $a\times b=-K$，$K\times a,L$ 和 $K\times b,N$ 均在叶平面内，双线性证明 $U_p$ 闭合。独立时三生成元线性独立；依赖时每个内部节点的叉积为零。

**约定 2.3（七维扩展的准确范围）。** 同样允许 $V=\operatorname{Im}\mathbb O$，其中 $\mathbb O$ 是正定范数的实除八元数代数，$u\times v=(uv-vu)/2$。Baez 的两生成结合性和 Darpö 的向量积配对／范数恒等式给引理2.2的同一证明；每个实际树及所有 $F^j(p)$ 都在同一二生成切面内。因此下文的全树结论也适用于这项解释。循环标架映射只在该三维切面上定义；不声称任意七维元组的递推、全 $SO(7)$ 等变或相应控制。七维版本使用标量三重积，不能写成七维行列式。

对固定 $p$，$E_p(\mathcal T)$ 可数且只是 $U_p$ 的子集；树码有限且可数。它不等于该切面、球面或线性张成。跨所有所供 $p$ 的像是 $V$，因为叶 $\alpha$ 可取任意 $a$；这个连续来源完全由额外制备端口供应。

## 3. 解释运输、实际参数像与不可逆性

**定理 3.1（原替换的全树运输）。** 对所有 $t\in\mathcal T,p\in\mathcal P,j\ge0$，

$$
E_p(\rho^jt)=E_{F^j(p)}(t).
$$

$F$ 的 Gram 更新为 $(A,B,C)\mapsto(B,\Delta,0)$。

证明。一阶两侧在 $\alpha$ 处同为 $b$、在 $\beta$ 处同为 $b\times a$，并保持同一个有序叉积节点；结构归纳使两侧对所有树相等。重复应用此等式给所有 $j$。$K\perp b$ 且 $|K|^2=\Delta$ 给 Gram 更新。实际执行仍是 $(\rho^jt,p)$，这个等式没有执行 $F$ 制备。

**定理 3.2（解释参数的实际像及完整纤维）。** 有

$$
F(\mathcal P)=\{(v,w):v\ne0,\ v\cdot w=0\}\cup\{(0,0)\}.
$$

对 $v\ne0$，任意这样的 $(v,w)$ 的全部原像恰为

$$
F^{-1}(v,w)=
\left\{\left(\frac{w\times v+\tau v}{|v|^2},v\right):\tau\in\mathbb R\right\};
$$

零像的纤维为 $\{(a,0):a\in V\}$。在

$$
\mathcal O=\{(u,v):u,v\ne0,\ u\perp v\}
$$

上 $F$ 是双射，数学逆为

$$
F^{-1}(v,w)=\left(-\frac{v\times w}{|v|^2},v\right).
$$

在独立制备域上，每个 $F^j,j\ge1$ 与 $F$ 有相同纤维。在全域上，每个 $j\ge2$ 的像为 $\mathcal O\cup\{(0,0)\}$，其零纤维恰为全部依赖制备。

证明。任何像都满足 $b\perp K$，而 $b=0$ 强迫 $K=0$。若 $v\ne0,w\perp v$，引理2.2给 $v\times(w\times v)=|v|^2w$，故 $a_0=(w\times v)/|v|^2$ 是一原像的第一坐标。范数式说明 $v\times(a-a_0)=0$ 当且仅当差平行于 $v$；以 $\tau=a\cdot v$ 参数化即得全部纤维。$v=0$ 强迫 $b=0$，$a$ 任意。

在 $\mathcal O$ 上纤维唯一的正交原像取 $\tau=0$，且非零，故所给逆确实在 $\mathcal O$ 内。独立制备一次进入 $\mathcal O$，后续在那里双射，不能再改变纤维。依赖制备先到 $(b,0)$，再到 $(0,0)$；独立制备永不为零。反复使用 $\mathcal O$ 中的逆使每个非零正交对在任意指定 $j$ 都实际可达，给全部像结论。

**命题 3.3（来源单射与解释损失分开）。** 原树替换 $\rho$ 单射；这不赋予 $F$、数值记录或实际源逆动作。

证明。复用 [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) 的原树接口与替换单射结论。其解码依据是：没有 $\rho$ 像为叶 $\alpha$；叶 $\beta$ 只来自 $\alpha$；$\langle\beta,\alpha\rangle$ 只来自 $\beta$，不能来自内部树，因为内部像的右孩子不可能为 $\alpha$。其它内部像分别对有序孩子递归解码，有限树归纳给单射。该解码是实际像上的数学恢复，与定理3.2的参数纤维不同。

## 4. 五符号归约与全树带符号尾递推

**定义 4.1（单位标签）。** 固定正交单位叶 $e_1,e_2$，令 $f_1=e_1,f_2=e_2,f_3=e_2\times e_1$。这是左手叉积标架；索引按模三循环。记

$$
\chi(t)=E_{(e_1,e_2)}(t)\in\{0,\pm f_1,\pm f_2,\pm f_3\}.
$$

复用 [Boundary Geometry 定理7.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) 的全树单位标签与循环运输：$R_0f_i=f_{i+1}$ 保持叉积，$\chi(\rho t)=R_0\chi(t)$。七值都由实际叶或有序节点实现。这个复用只针对该固定单位解释。

**引理 4.2（全制备五符号表与初值符号）。** 对任意 $p$，以下为完整上三角叉积表；同符号乘积为零，反序取负。

| 4符号 $\times$ | $b$ | $K$ | $L$ | $N$ |
| --- | --- | --- | --- | --- |
| 4表 $a$ | $-K$ | $-L$ | $AK$ | $CK$ |
| 4表 $b$ | — | $-N$ | $CK$ | $BK$ |
| 4表 $K$ | — | — | $-\Delta a$ | $-\Delta b$ |
| 4表 $L$ | — | — | — | $-\Delta K$ |

每棵树可递归选择一个恒等于 $E_p(t)$、对所有 $p$ 同时有效的描述子：零，或

$$
\varepsilon A^iB^jC^h\Delta^\ell Z,
\quad \varepsilon\in\{\pm1\},\ i,j,h,\ell\in\mathbb N,
\quad Z\in\{a,b,K,L,N\}.
$$

描述子不要求唯一。所选描述子非零且 $h=0$ 恰等价于 $\chi(t)\ne0$。在 $\Delta>0$ 时：若 $\chi(t)=\sigma f_1$，初值为 $\sigma$ 乘一个严格正数再乘 $a$ 或 $N$；若标签为 $\sigma f_2$，初值相应为 $\sigma$ 乘正数再乘 $b$ 或 $-L$；若标签为 $\sigma f_3$，初值为 $\sigma$ 乘正数再乘 $K$。

证明。前几项由定义和反序符号得到。代入 $L=Ca-Ab,N=Ba-Cb$，得到 $a\times L=AK,a\times N=CK,b\times L=CK,b\times N=BK$。$K\perp a,b$ 给 $K\times(K\times a)=-\Delta a$ 及对应的 $b$ 式。最后双线性展开

$$
(Ca-Ab)\times(Ba-Cb)=-(AB-C^2)K.
$$

这证明十个非对角项。叶描述子为 $a,b$；在节点处相乘子描述子的单项式，再查此完整表，零孩子或同符号即为零，其余仍有要求的形状。结构归纳不作任何除法，覆盖 $C=0$ 或 $\Delta=0$。

在单位参考处 $A=B=\Delta=1,C=0,L=-f_2,N=f_1$，五个符号都非零，故描述子恰在零或正 $C$ 次数时消失。$\Delta>0$ 且 $h=0$ 时 $A,B,\Delta$ 均正，单位处的方向和符号给所列三类。零标签的树在非正交制备处仍可有非零初值，不能把它在所有制备处判成零。

**定理 4.3（全树尾的实际标架与递推）。** 设 $\Delta>0$，置 $r=\sqrt B,s=\sqrt\Delta$ 以及

$$
g_1=b/r,\qquad g_2=K/s,\qquad g_3=N/(rs).
$$

它们是 $U_p$ 中的左手正交单位标架。令 $R$ 循环 $g_i$，则 $R$ 保持切面内叉积。若 $\nu(t)=(m,n)$、$\chi(t)=\sigma f_i\ne0$，则

$$
\begin{aligned}
x_1&=\sigma r^m s^n g_i,\\
x_2&=\sigma s^m(rs)^n g_{i+1},\\
q_{j+2}&=q_jq_{j+1},\qquad q_j=|x_j|\quad(j\ge1),\\
x_{j+2}&=\sigma(x_{j+1}\times x_j)=|x_j|R x_{j+1}\quad(j\ge1).
\end{aligned}
$$

若 $\chi(t)=0$，全部 $x_j,j\ge1$ 为零。若 $\Delta=0$，全部 $x_j,j\ge2$ 为零。

证明。$K\perp b,N=K\times b$ 且 $|N|^2=B\Delta$ 给正交单位性。叉积表为 $g_{i+1}\times g_i=g_{i+2}$，所以循环保持乘法。按叶数的结构归纳给齐次性

$$
E_{(r g_1,s g_2)}(t)=r^m s^n\chi_g(t),
$$

其中 $\chi_g$ 将 $f_i$ 换成 $g_i$，并保持零及符号。定理3.1把 $x_1$ 写为此式，$x_2$ 则使用叶对 $(s g_2,rs g_3)$。此后每次标签循环，组成按 $M$ 更新。由 $M^2=M+I$，相隔两步的每个指数是前两步指数之和，故正幅度满足乘法递推；标架表和 $\sigma^2=1$ 给带符号叉积式。零标签在正交的 $F(p)$ 处齐次求值为零，之后仍零。依赖分支的 $F^2(p)=0$ 给第二项后的全零结论。

## 5. 无校准三次向量读取的尖锐全树闭合

**定理 5.1（初始三读的全称恢复式）。** 规定 $\operatorname{sgn}(0)=0$。对每个实际 $t,p$ 都有

$$
x_3=\operatorname{sgn}\bigl(x_0\cdot(x_2\times x_1)\bigr)(x_2\times x_1).
$$

在三维中符号也可写为 $-\operatorname{sgn}\det(x_0,x_1,x_2)$。令 $W_3(t,p)=(x_0,x_1,x_2)$、$\mathcal B_3=W_3(\mathcal J)$，则其实际像上的后继为

$$
G(x,y,z)=\bigl(y,z,\operatorname{sgn}(x\cdot(z\times y))(z\times y)\bigr).
$$

任意两个实际来源，即使树和制备都未知，$W_3$ 相同当且仅当包含时刻零的完整向量 $\rho$ 未来相同。任意长度至少三的连续初始记录也决定完整未来。

证明。先取 $\Delta>0$、非零标签 $\sigma f_i$。令 $w=x_2\times x_1$；定理4.3给 $w$ 是 $g_{i+2}$ 的严格正倍数，$x_3=\sigma w$。须由初值确定 $\sigma$。若 $i=1$，$w$ 是 $N$ 的正倍数，而引理4.2的两种初值方向满足 $a\cdot N=\Delta>0,N\cdot N=B\Delta>0$。若 $i=2$，$w$ 是 $b$ 的正倍数，$b\cdot b=B>0,(-L)\cdot b=\Delta>0$。若 $i=3$，两者所用方向为 $K$，$|K|^2=\Delta>0$。每种情况都给 $\operatorname{sgn}(x_0\cdot w)=\sigma$。

零标签时 $x_1=x_2=x_3=0$，尽管 $x_0$ 可能非零；依赖制备时 $x_2=x_3=0$。这两分支的 $w$ 均为零，所以公式仍成立。在三维 $x_0\cdot(x_2\times x_1)=-\det(x_0,x_1,x_2)$，给等价符号。

将同一全称公式依次应用于实际树 $\rho t,\rho^2t,\ldots$，得 $G(W_3(t,p))=W_3(\rho t,p)$，后继仍实际可达。归纳恢复所有后项；反向完整未来相同包含前三项。较长记录的末三项恢复继续的后项，而原有前缀保留时刻零。此证明只断言 $\mathcal B_3$ 的闭合，没有断言任意环境三元组可达。

**命题 5.2（同一制备的两读反例与窗口下界）。** 在全树连续窗口约定下，三是统一最短长度；甚至一个固定制备即可反驳长度二的闭合。取

$$
a=(5/4,0,0),\quad b=(3/4,1,0),\quad
\lambda=25/16,
$$

则 $A=B=\Delta=\lambda,C=15/16$。令 $k=\langle\beta,\alpha\rangle$、

$$
t_A=\langle\alpha,\langle k,\alpha\rangle\rangle,
\qquad t_B=\langle\beta,\langle k,\beta\rangle\rangle.
$$

二者前三项为

$$
\begin{array}{c|ccc}
&x_0&x_1&x_2\\\hline
t_A&AK&BN&\Delta^2b\\
t_B&BK&\Delta N&B\Delta^2b
\end{array}
$$

前两项相同，第三项不同。

证明。引理4.2给初值 $AK,BK$。在 $F(p)$ 处 $A'=B,B'=\Delta,K'=N$，得到第二项。在 $F^2(p)$ 处 $A''=\Delta,B''=B\Delta,K''=N\times K=\Delta b$，得到第三项；$b\ne0,\lambda\ne1$ 排除相等。因而两窗口的实际后继不能为函数。将二树各先替换一次，当前值相同、下一值不同，排除一窗口闭合；零观察由 $\alpha$ 与 $\langle\alpha,\alpha\rangle$ 的初值不同排除。三窗口充分性由定理5.1给出。这是全树的统一连续窗口界，不是每个制备分别的最短界、任意编码的存储界或规范轨道的界。

**命题 5.3（数值后继无逆及规范轨道例外）。** 在 $C\ne0,\Delta>0$ 时，树

$$
t=\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle
$$

有初值 $CK$、零标签，故 $W_3(t,p)=(CK,0,0)$。零 cherry $\langle\alpha,\alpha\rangle$ 的记录为 $(0,0,0)$；两者经 $G$ 均到零。因此 $G$ 没有实际像上的逆。

另在规范来源 $T_j=\rho^j\alpha$ 上，原结构关系为 $T_{j+2}=\langle T_{j+1},T_j\rangle$，所以对所有 $p$ 有 $E_p(T_{j+2})=E_p(T_{j+1})\times E_p(T_j)$。这个已知规范轨道的二值递推不延伸到全部树；命题5.2给了实际反例。它也没有赋予 Clifford 叶积的逆或六周期。

## 6. 实际联合像、纤维和同制备上下文

**定理 6.1（三向量像与组成标记的两向量像）。** 固定 $p$，$\mathcal B_{3,p}=W_3(\mathcal T\times\{p\})$ 恰为 $V^3$ 中由

$$
(a,b,K),\qquad(b,K,N)
$$

生成的最小逐坐标有序叉积子 magma。未知制备像为 $\bigcup_p\mathcal B_{3,p}$。

另一实际记录为 $\eta_p(t)=(\nu(t),E_p(t),E_p(\rho t))$。定义

$$
D_p(0,0)=\varnothing,\quad D_p(1,0)=\{(a,b)\},\quad
D_p(0,1)=\{(b,K)\}.
$$

对 $m+n\ge2$，$D_p(m,n)$ 为所有有序非空分拆 $(m,n)=d+e$ 的以下集合之并：

$$
\{(u\times u',v\times v'):(u,v)\in D_p(d),\ (u',v')\in D_p(e)\}.
$$

则 $\eta_p(\mathcal T)$ 恰为 $\bigcup_{m+n\ge1}\{(m,n)\}\times D_p(m,n)$，每个 $D_p(m,n)$ 有限并带实际树见证。

证明。解释和 $\rho$ 都保持有序节点，故 $W_3(\langle s,t\rangle,p)$ 是两子记录的逐坐标叉积。结构归纳给生成集合的一侧包含，反向将任意有限生成表达式解释成对应原树。两向量递归的一侧包含用实际根分拆；反向对叶数归纳，为所选两个孩子记录取得实际树，再在同一 $p$ 下有序 graft。每个分拆的孩子叶数严格减少，有限分拆及有限子集合保证有限性。这里未将两个边缘像改成自由乘积或线性张成。

组成为 $(m,n)$ 的原树数直接复用 GenealogicalFiberTransport 的

$$
\operatorname{Catalan}_{m+n-1}\binom{m+n}{m}\quad(m+n\ge1).
$$

其来源对应为：$L=m+n$ 个有序叶的满二叉形状有 $\operatorname{Catalan}_{L-1}$ 种，每形状选择 $m$ 个叶位标 $\alpha$。求值可合并这些树，不能把此数当作 $|D_p(m,n)|$。零组成的实际来源纤维为空，不套用自然数减法总化的数值表达式。

**定理 6.2（固定制备的严格单孔上下文）。** 固定 $p$，允许有限上下文

$$
\mathsf C::=\square\mid\rho\mathsf C\mid
\langle u,\mathsf C\rangle\mid\langle\mathsf C,u\rangle,
\qquad u\in\mathcal T,
$$

旁树 $u$ 使用同一制备。两树的 $W_3$ 相同，当且仅当每个这种上下文的当前向量读数相同。

证明。相等记录经 $G$ 保持相等；graft 时旁树的同一实际记录逐坐标相乘也保持相等。按上下文结构归纳得到其当前输出相同。反向取 $\square,\rho\square,\rho^2\square$ 恢复三坐标。这是对每个静态反事实上下文的全称比较，不是在一个破坏性源上实际执行所有上下文。

**命题 6.3（未知制备与配对合法性的边界）。** 跨制备的 $W_3$ 相等足以保持 $\rho$ 未来，却不足以保持使用各自原叶的全部上下文。取同一树 $\beta$，

$$
p=(e_1,e_2),\qquad p'=(e_1+\lambda e_2,e_2),\quad\lambda\ne0.
$$

二者记录都是 $(e_2,-e_3,e_1)$。上下文 $\langle\alpha,\langle\alpha,\square\rangle\rangle$ 却分别给 $-e_2$ 和 $\lambda e_1-e_2$。

证明。两制备有相同 $b,K,N$。后一个上下文为 $a\times(a\times b)=Ca-Ab$；代入各自的 $A,C$ 得所列不等输出。使用的是各自原标签的旁树，未加入任意外部向量。

两个待配对句柄必须实际同制备；单凭数值 $W_3$ 或 $\eta$ 不能判断该守卫，因为零 cherry 在每个制备处都给零向量记录及同一组成。须另保留权威共同制备身份，或确实所供的 $p$；身份本身不供应数值校准。不合法配对应记录独立失败符号，区别于成功零输出。新增部分操作要下降时，其定义域与后继行为必须在实际联合记录纤维上恒定；这是 [Continuation 定理13.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的合法域饱和条件，而非创建句柄或复制来源的权限。

**定理 6.4（固定制备完整数值响应的精确纤维）。** 对 $\Delta>0$，记 $r=\sqrt B,s=\sqrt\Delta$。

1. 若 $\chi(t)=0$，同一完整响应纤维恰由满足 $\chi(u)=0,E_p(u)=E_p(t)$ 的树组成。
2. 若 $\chi(t)\ne0$ 且 $(r,s)\ne(1,1)$，纤维恰由 $\nu(u)=\nu(t),\chi(u)=\chi(t),E_p(u)=E_p(t)$ 的树组成。
3. 若 $\chi(t)\ne0$ 且 $r=s=1$，纤维恰由 $\chi(u)=\chi(t),E_p(u)=E_p(t)$ 的树组成，组成可不同。

证明。零标签尾全零，非零标签尾非零，所以两分支不混合。非零分支的 $x_1$ 方向确定同一标签索引及符号。若两组成之差为 $(d_m,d_n)$，$x_1,x_2$ 幅度相同给

$$
\begin{aligned}
d_m\log r+d_n\log s&=0,\\
d_n\log r+(d_m+d_n)\log s&=0.
\end{aligned}
$$

非零整数差时行列式 $d_m^2+d_md_n-d_n^2\ne0$：$d_n=0$ 直接成立，$d_n\ne0$ 时若为零，会使有理数 $d_m/d_n$ 等于无理根 $(-1\pm\sqrt5)/2$。因此非零差迫使两对数为零。非单位 $(r,s)$ 只能有零组成差；单位分支的全部尾幅度为一，只由标签决定。反向用定理4.3恢复各尾，再用初值条件补时刻零；零标签分支只有初值条件。

**命题 6.5（全部退化纤维与语法遗失）。** 当 $\Delta=0,b\ne0$，恰有三种不同完整记录：叶 $\alpha$ 的 $(a,b,0)$，叶 $\beta$ 的 $(b,0,0)$，全部内部树的 $(0,0,0)$。当 $b=0,a\ne0$，只有 $\alpha$ 为 $(a,0,0)$，其它树全零；$a=b=0$ 时全树合并。

证明。依赖叶的每个内部叉积为零；$F(p)=(b,0),F^2(p)=0$ 给三个坐标，所列非零条件区分各类。对未知制备，一给定实际记录 $(x,y,z)$ 的纤维准确写为

$$
\bigcup_{t\in\mathcal T}
\{(t,p):E_p(t)=x, E_{F(p)}(t)=y, E_{F^2(p)}(t)=z\}.
$$

每个指定树贡献有限组关于 $p$ 的多项式坐标方程；这个并只取实际树与允许制备，不断言一般唯一性。

任何上述行为记录都不能恢复完整语法。$\langle\alpha,\alpha\rangle$ 与 $\langle\beta,\beta\rangle$ 在每个 $p$ 都为零但组成不同；三个 $\alpha$ 的两种括号均为零但形状不同；$\langle\langle\alpha,\alpha\rangle,\langle\beta,\beta\rangle\rangle$ 与反序接合组成同为 $(2,2)$、全响应零但原树不同。这些也是后文全参数符号记录的实际反例。

## 7. 实际尾像及条件二值补充

**定义 7.1（已替换来源的尾记录）。** 取 $\mathcal X_1=\rho(\mathcal T)\times\mathcal P$，当前源的向量及下一向量记为 $y,z$。非零尾的单位标签符号记为 $\epsilon\in\{\pm1\}$；若 $z\times y=0$ 则统一记 $\epsilon=+1$。目标为当前及全部后续向量，记录为 $\theta=(y,z,\epsilon)$。

**定理 7.2（尾记录的精确实际像与尖锐二值区别）。** 有

$$
\theta(\mathcal X_1)=
\{(y,z,\epsilon):y,z\ne0,\ y\perp z,\ \epsilon\in\{\pm1\}\}
\cup\{(y,0,+1):y\in V\}.
$$

不存在实际 $(0,z),z\ne0$。非零分支后继为 $(z,\epsilon(z\times y),\epsilon)$，零下一值分支后继为 $(0,0,+1)$。固定任一非零正交数值对 $(y,z)$，恰有两个完整未来类；在 $(y,0)$ 上恰有一个。相对于已保留精确 $y,z$ 的配对记录，二值补充必要且充分。

证明。定理4.3给非零尾的正交连续向量和带符号递推；零标签尾全零；依赖制备的已替换当前值可非零，但下一项和以后全零。这给像的一侧包含及不存在 $(0,z\ne0)$。

反向对任意非零正交 $y,z$，取当前树 $\beta=\rho\alpha$，供应 $b=y,a=-y\times z/|y|^2$，得到当前和下一值 $y,z$，标签符号为正。为实现负号，令 $t_* =\langle\beta,\langle\beta,\alpha\rangle\rangle$，其单位标签为 $-f_1$。置

$$
Y=|y|^2,\quad Z=|z|^2,\quad
D_0=Y^2/Z,\quad B_0=Z^2/Y^3,
$$

并供应

$$
b=-y/D_0,\qquad K=-z/(B_0D_0),\qquad a=(K\times b)/B_0.
$$

直接算得 $b\perp K,|b|^2=B_0,|K|^2=D_0$。引理2.2给 $b\times a=K$，故是实际制备。树 $t_*$ 的通式为 $-N$，因此当前树 $\rho t_*$ 的值为 $-D_0b=y$，下一值为 $-B_0D_0K=z$，其标签符号为负。两个见证共享同一数值对，未要求它们制备相同。任意 $y$ 的 $(y,0,+1)$ 由当前 $\beta$ 和制备 $(0,y)$ 实现。七维时每个构造仍在其二生成切面内。

非零对的两种第三值 $\pm(z\times y)$ 不同；指定符号后递推确定全尾，所以恰两类。零下一值时全序列为 $y,0,0,\ldots$，只有一类。必须以至少两个记录值区分两类，记录 $\epsilon$ 达到此界；这仅是条件一位区别，不是两个精确实向量的有限位成本、任意编码的存储下界或读原语最小性。

**命题 7.3（尾的付费取得与同制备接合）。** 三次尾向量读、两次 $\rho$ 得 $y,z,w$，可取得

$$
\epsilon=\frac{w\cdot(z\times y)}{|z\times y|^2}
$$

在非零分支上的准确 $\pm1$；零分支取 $+1$。两次连续尾读不能统一确定下一向量，定理7.2的两实际见证即为反例。若另供原树码，可从码算单位符号，树码权限仍单独计费。对任意初始来源，定理5.1用 $W_3$ 算其未来尾符号，无须第四次初始向量读。

两个实际同制备尾记录可接合：令

$$
\begin{aligned}
Y&=y_s\times y_t,&Z&=z_s\times z_t,\\
W&=[\epsilon_s(z_s\times y_s)]\times[\epsilon_t(z_t\times y_t)].
\end{aligned}
$$

若 $Z\times Y=0$，新符号取 $+1$；否则取 $W\cdot(Z\times Y)/|Z\times Y|^2$。

证明。三读商公式由定理7.2的实际第三值给出。$\rho(\mathcal T)$ 对同制备接合闭合，因为 $\langle\rho s,\rho t\rangle=\rho\langle s,t\rangle$。三个所列接合值正是该实际树的连续输出，故定理4.3保证非零商为 $\pm1$，并给正确第三值及像内闭合。零分支的下一项以后全零。此结论保留实际同制备守卫，不声称任意环境 $\theta$ 元组可以合法接合。

## 8. 已校准的数量与向量联合两读

**定义 8.1（新增数量口与校准合同）。** 本节固定公共校准 $p$；每次 Read 返回 $q(t)=2m+3n$ 及 $E_p(t)$。数量是同一树的加法组成观察，向量节点仍为叉积。两次联合读的数量为 $r_0=2m+3n,r_1=3m+5n$，复用 Atomic5.4／13.3 的整数逆

$$
m=5r_0-3r_1,\qquad n=2r_1-3r_0.
$$

故取得 $\eta_p(t)=(\nu(t),u,v)$，$u=x_0,v=x_1$；其实际域是定理6.1的组成标记像。

**定理 8.2（校准联合边界的后继与上下文）。** $\Delta>0$ 时使用定理4.3的校准 $R,r,s$，置 $\lambda=s/r,\mu=r$，则

$$
(\nu,u,v)\longmapsto(M\nu,v,\lambda^m\mu^nRv).
$$

$\Delta=0$ 时后继为 $(M\nu,v,0)$。同制备有序构造为

$$
(\nu,u,v),(\zeta,z,w)\longmapsto(\nu+\zeta,u\times z,v\times w).
$$

在该固定校准实际域，$\eta$ 相等当且仅当完整数量／向量联合 $\rho$ 未来相同，也当且仅当全部定理6.2型上下文的联合输出相同。

证明。$F(p)$ 的叶对为 $(b,K)$，下一叶对为 $(K,N)=(\lambda Rb,\mu RK)$。结构归纳的齐次性与 $R$ 的叉积相容给

$$
E_{F^2(p)}(t)=\lambda^m\mu^nR E_{F(p)}(t).
$$

依赖分支 $F^2(p)=0$，不需除法或标架。组成按 $M$ 更新，$\rho$ 与接合相容，得所列构造。相同记录逐操作保持相同，归纳给联合未来及上下文输出相同。反向首两联合输出用整数逆取得 $\nu,u,v$；上下文取洞及一次替换即可。每个后继和接合都有原树见证，未扩张实际域。

**推论 8.3（原始正交制备的较小校准记录）。** 若原 $a,b$ 非零且正交，取初始标架 $(a/\sqrt A,b/\sqrt B,K/\sqrt{AB})$ 的循环 $R_p$、$\lambda=\sqrt{B/A},\mu=\sqrt A$，则

$$
(\nu,u)\longmapsto(M\nu,\lambda^m\mu^nR_pu).
$$

证明。叶对满足 $F(p)=(\lambda R_pa,\mu R_pb)$，同一结构齐次归纳即得。单位正交情形就是复用的单位标签／组成闭合。这项特例仍收费校准，不能改成全制备结论。

**命题 8.4（校准非正交实例的尖锐取得与初值档案）。** 令 $h=a\times b=-K$，取原六叶树

$$
\begin{aligned}
X&=\langle\alpha,\langle\beta,\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle\rangle\rangle,\\
Y&=\langle\alpha,\langle\langle\alpha,\beta\rangle,
\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle\rangle.
\end{aligned}
$$

二者组成均为 $(3,3)$，且 $E_p(X)=C^2h,E_p(Y)=\Delta h$。在公共校准 $p=(e_1,e_1+e_2)$ 处，首联合读均为 $(15,e_3)$，下一向量分别为零和 $(-2,2,0)$。因此恢复全初始联合行为在这个实例至少一次更新；两读一次更新达到。

证明。置 $z=b\times h=Ba-Cb$。$a\times z=-Ch,h\times z=\Delta b$，故 $X$ 为 $a\times[b\times(a\times z)]=C^2h$，$Y$ 为 $a\times(h\times z)=\Delta h$。在指定制备 $A=1,B=2,C=\Delta=1$；$F(p)$ 有 $C'=0,\Delta'=2,h'=b\times K=(-1,1,0)$，得到下一项。零更新重复读无法分开二者。

读调用下界也为二，即使允许唯一读在非初始时刻。树

$$
U=\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle,
\qquad V_0=\langle\langle\alpha,\beta\rangle,\langle\alpha,\beta\rangle\rangle
$$

组成同为 $(2,2)$，初值分别为 $CK$ 和零，一阶后全部向量均零，全部数量以后也相同。在这固定校准处，一次读以前的确定 $\rho$ 日程源无关：若读在零时刻，$X,Y$ 反驳正确性；若读在任何后时刻，$U,V_0$ 反驳正确性。无读更不能恢复非恒定目标。两读一次更新由定理8.2达到。这不声称每个校准、任意编码口或更宽菜单都有该下界。$U,V_0$ 同时说明仅保留组成及下一向量一般会遗失初值，$u$ 必须另保留。

**命题 8.5（同树同组成仍不能免校准）。** 取 $t=\langle\alpha,\langle\alpha,\beta\rangle\rangle$，其组成 $(2,1)$、两数量 $(7,11)$。供应

$$
p_0=(e_1,e_2),\qquad
p_1=\left(2e_1,\frac{\sqrt{31}e_1+e_2}{4}\right).
$$

两制备的 $(x_0,x_1)$ 都为 $(-e_2,e_3)$，而 $x_2$ 分别为 $-e_1$ 和 $(-e_1+\sqrt{31}e_2)/32$，故未知制备两联合读不能统一预测下一项。

证明。树通式为 $L=Ca-Ab$，其一阶式为 $-BK$，二阶式为 $-\Delta N$。$p_1$ 的 $A=4,B=2,C=\sqrt{31}/2,\Delta=1/4,K=-e_3/2,N=(e_1-\sqrt{31}e_2)/8$，直接代入得所列三项。树码和组成均相同，遗漏的条件确实是校准。无校准定理5.1通过新增一次向量读解决预测任务，未免费取得校准。

## 9. 全参数多项式语义与实际符号像

**定义 9.1（Gram 多项式记录）。** 本节将基向量记为 $h=a\times b$，避免与组成 $\nu$ 混用。令 $\mathscr R=\mathbb Z[A,B,C]$。每棵树递归生成三多项式 $z(t)=(P_t,Q_t,T_t)$，叶记录为 $(1,0,0),(0,1,0)$。对 $u,v\in\mathscr R^3$ 置 $d_{ij}=u_iv_j-u_jv_i$，定义

$$
J(u,v)=(Bd_{23}-Cd_{31},\ -Cd_{23}+Ad_{31},\ d_{12}),
\qquad z(\langle s,t\rangle)=J(z(s),z(t)).
$$

**定理 9.2（全制备唯一表示）。** 对所有树及所有制备，包括依赖制备，

$$
E_p(t)=P_t(A,B,C)a+Q_t(A,B,C)b+T_t(A,B,C)h.
$$

三多项式作为全制备表示唯一。实际符号像 $\mathcal Z_{\rm src}$ 恰为两个叶三元组生成的最小 $J$ 子 magma，不是整个 $\mathscr R^3$。

证明。$h\times a=Ab-Ca,b\times h=Ba-Cb$，将两线性组合的叉积按这三条基对展开，正是 $J$。结构归纳证明存在性且不除任何可能为零的量。

若两三元组对所有制备给相同向量，对每个 $A>0,B>0,C^2<AB$ 取

$$
a=(\sqrt A,0,0),\qquad
b=(C/\sqrt A,\sqrt{B-C^2/A},0).
$$

$a,b,h$ 线性独立，故每个系数差在这个非空开 Gram 域为零。开域中取一个开长方体，固定除一变量外的变量，一元多项式在区间上为零就全系数为零；再依次对其它变量重复，得到原多项式为零。这证明全称唯一性，不断言单个退化制备能识别系数。七维可在嵌入的三维二生成切面作同一测试。像的一侧包含用结构递归，反向每个有限 $J$ 表达式就是对应原树。

**命题 9.3（原替换的半线性符号后继）。** 定义 $\mathfrak h(f)=f(B,\Delta,0)$，则

$$
\Sigma(P,Q,T)=(-B\mathfrak h(T),\ \mathfrak h(P)+C\mathfrak h(T),\ -\mathfrak h(Q)),
\qquad z(\rho t)=\Sigma z(t).
$$

$\Sigma$ 可加且为 $\mathfrak h$ 半线性，不是 $\mathscr R$ 线性。记录 $z$ 由 $J,\Sigma$ 决定所有全制备未来及同制备有编码上下文。

证明。$F(p)$ 的叶对是 $(b,-h)$，Gram 为 $(B,\Delta,0)$，其第三基向量为 $b\times(-h)=-Ba+Cb$。代入定理9.2并收集 $a,b,h$ 系数得所列公式；全称唯一性给与实际 $\rho$ 的交换式。两种递归保持实际符号像。这个记录取得自有限树码，不是有限数值读的结果。

## 10. 全称第一损失、剩余记录与精确恢复

**定义 10.1（零相关截面与正交后继）。** 令 $\mathscr R_0=\mathbb Z[A,B]$，$H$ 将每个系数限制到 $C=0$，$i:\mathscr R_0^3\to\mathscr R^3$ 为系数包含。定义

$$
\mathfrak h_0(f)=f(B,AB),\qquad
\Theta(P,Q,T)=(-B\mathfrak h_0(T),\ \mathfrak h_0(P),\ -\mathfrak h_0(Q)).
$$

准确的关系为

$$
H\Sigma=\Theta H.
$$

完整环上的 $\mathfrak h$ 分解为 $\widetilde{\mathfrak h}H$，其中 $\widetilde{\mathfrak h}:\mathscr R_0\to\mathscr R$ 取 $f(A,B)\mapsto f(B,AB-C^2)$；$H\widetilde{\mathfrak h}=\mathfrak h_0$。它不等于直接将 $\mathfrak h_0H$ 包含回完整环，例如 $\mathfrak h(B)=AB-C^2$。

**引理 10.2（正交符号后继单射）。** $\mathfrak h_0$ 及 $\Theta$ 都单射。

证明。单项式 $A^iB^j$ 被 $\mathfrak h_0$ 送到 $A^jB^{i+j}$；两个非负指数对的像相同必有相同 $j$ 再有相同 $i$，所以不同单项式不碰撞，系数不能抵消。$\Theta$ 的零值强迫三个 $\mathfrak h_0$ 值为零，因为 $\mathscr R_0$ 为整环，乘 $B$ 无核；再用 $\mathfrak h_0$ 单射。

**定理 10.3（全符号模块的核及实际树无新增后期损失）。** 在 $\mathscr R^3$ 上，

$$
\ker\Sigma=C\mathscr R^3.
$$

对任意实际树 $s,t$ 以及每个整数 $n\ge1$，以下三条件等价：

$$
\begin{gathered}
\forall p\in\mathcal P,\quad E_p(\rho^ns)=E_p(\rho^nt),\\
H z(s)=H z(t),\\
z(s)-z(t)\text{ 的每个系数坐标都被 }C\text{ 整除}.
\end{gathered}
$$

证明。若 $Hz=0$，每个坐标都被 $C$ 整除，在 $\mathfrak h$ 的 $C\mapsto0$ 代入下为零，故 $\Sigma z=0$。反向 $\Sigma z=0$ 给 $\Theta Hz=H\Sigma z=0$，引理10.2给 $Hz=0$。多项式在 $C=0$ 处为零恰等价于每个项含正 $C$ 次数，即被 $C$ 整除，得核公式。

对树差，若 $H(z(s)-z(t))=0$，第一次 $\Sigma$ 已消去差，以后仍零。反向全制备的第 $n$ 项相同，由定理9.2唯一性给 $\Sigma^n(z(s)-z(t))=0$；限制到 $C=0$ 得 $\Theta^nH(z(s)-z(t))=0$，逐次单射迫使原截面差为零。这证明每个 $n$ 的全称等价。它是实际子 magma 上的碰撞判据，不声称模块中每个元素或每个 $C$ 倍数都有原树见证；固定数值制备可有更多碰撞，属不同关系。

实际第一损失非空：命题5.3所列树（亦即命题8.4的 $U$）有 $z(U)=(0,0,-C)$，而零 cherry 的记录为零；两树一次替换后对每个制备都为零。在 $p=(e_1,e_1+e_2)$ 处原初值分别为 $-e_3$ 和零。这个原树见证区别于只在环境多项式模块中计算核。

**定理 10.4（可访问剩余记录的全称恢复）。** 若另供原始树码，可定义有限多项式剩余记录

$$
\mathcal L(t)=\frac{z(t)-iH z(t)}C.
$$

从已访问的 $\Sigma z(t)$ 及 $\mathcal L(t)$，可唯一恢复 $z(t)$，从而恢复其全制备语义及全部编码上下文行为。

证明。分子限制到 $C=0$ 为零，逐坐标准确整除。先由 $H\Sigma z(t)=\Theta Hz(t)$ 在实际 $\Theta$ 像上反演。对 $\Theta(P,Q,T)$，首坐标准确除以 $-B$ 得 $\mathfrak h_0(T)$，第二坐标为 $\mathfrak h_0(P)$，第三取负为 $\mathfrak h_0(Q)$。其单项式逆为

$$
A^uB^v\longmapsto A^{v-u}B^u\quad(v\ge u)
$$

且每个实际坐标都满足此像条件。引理10.2保证逆唯一。最后 $z(t)=iHz(t)+C\mathcal L(t)$。恢复的是全称语义记录，不是原树语法或物理制备。

**命题 10.5（有限码与无统一符号预算）。** 每树给有限多项式且递归终止；树码长度、次数、展开系数长度与存储无全树统一上界。一个实际族为 $k=\langle\beta,\alpha\rangle$、$t_0=\alpha$、$t_{j+1}=\langle k,\langle k,t_j\rangle\rangle$，满足

$$
z(t_j)=((-\Delta)^j,0,0),\qquad\text{叶数}=1+4j.
$$

证明。$K\perp a$，引理2.2给 $K\times(K\times a)=-\Delta a$，归纳得到向量式及唯一多项式式，每步增加四叶。展开 $(AB-C^2)^j$ 的次数增长，$j+1$ 个二项系数绝对值总和为 $2^j$，所以至少一个不小于 $2^j/(j+1)$，其长度无界。其它表示可压缩此族，不据此声称所有表示的同一复杂度下界；这里只给展开多项式及树码的界限。准确整除、代入及递归都按声明有限表示付费，没有从一次数值 Read 或未授予的参数扫描取得全称记录，也没有统一有限位预算或维数最小性声明。

## 11. 原始制备的目标纤维与额外档案

**定理 11.1（静态全树尾与规范尾的制备纤维）。** 目标固定为原始 $p=(a,b)$。静态全当前族 $(E_p(t))_{t\in\mathcal T}$ 的制备纤维为单点。静态全后替换族

$$
\Phi(p)=(E_p(\rho^jt))_{t\in\mathcal T,j\ge1}
$$

的纤维恰为定理3.2的 $F$ 纤维。已知规范尾从 $T_1=\beta$ 开始的完整数值序列也有同一纤维。

证明。全当前族的两个叶坐标就是 $a,b$。相同 $F(p)$ 经定理3.1给全部后替换值相同；反向全族的 $(\alpha,j=1),(\beta,j=1)$ 坐标就是 $b,K$，强迫相同 $F(p)$。规范尾的首两值也是 $b,K$，以后由规范叉积递推决定，故纤维相同。这里比较静态信息，不供应同时读取全部树的实验。

**定理 11.2（原始剪切的准确补充记录）。** 在 $b\ne0$ 域，另供应或在制备时确实保留 $\tau=a\cdot b$，则尾记录 $(b,K,\tau)$ 恢复

$$
a=\frac{K\times b+\tau b}B.
$$

这包括 $K=0$ 的依赖分支。一般额外可访问记录 $Z$ 充分，当且仅当其在每个允许的实际 $F$ 纤维上单射。在无限制 $b\ne0$ 域，一个实标量足够；没有附加数据不够，有限或可数附加字母表也不够。

证明。定理3.2给完整仿射直线纤维，$K\times b=Ba-Cb$，代入 $\tau=C$ 得逆式。任意 $a+\lambda b$ 保持 $b,K$ 及全尾，原制备却不同，排除无附加记录。一般判据复用准确纤维原则：同一非空联合记录纤维若含两个不同制备，解码不能同时正确；若每个纤维恰一个制备，则取该唯一值解码。每条无限制仿射实线不可数，不能单射到有限或可数字母表。这不设定任意不连续实编码的维数下界。

**命题 11.3（零叶及取得合同的退化边界）。** 若 $b=0$，$F(p)=0,\tau=0$ 与 $a$ 无关，必须另保留在 $a$ 上单射的记录；保留 $a$ 足够。在线性实记录 $V\to\mathbb R^d$ 约定下，秩—零度强迫 $d\ge\dim V$，主版本为三，七维版本为七。受限制备域可缩小纤维并改变该要求。

已知从 $T_1$ 开始的具体取得是 Read$(b)$、$\rho$、Read$(K)$；$\tau$ 须另供或由获准的早期测量保留，尾计算不能生成它。$b\ne0,K=0$ 时须保留首读 $b$，再更新的 $F^2(p)=0$ 会丢失它。若已知初始是 $\alpha$，两读在 $\alpha,\beta$ 直接得 $(a,b)$，是不同起始合同。若原树任意未知，零 cherry 对所有制备有全零未来，无限多个 $\rho$ 数值读也不保证提供任何制备信息。这些结论分别由定理3.2及实际树求值给出。

## 12. 已知节点上的破坏性制备取得

**定理 12.1（已知原节点的实际像与完整制备纤维）。** 从已知字面节点 $T_2=\langle\beta,\alpha\rangle$ 开始，未知 $p$。在节点及一次 $\rho$ 后两读记为

$$
u=K,\qquad v=N=K\times b.
$$

独立制备的准确像是全部非零正交 $(u,v)$；依赖制备全部给 $(0,0)$，无其它退化对。非零对的完整制备纤维为

$$
b=-\frac{u\times v}{|u|^2},\qquad
B=\frac{|v|^2}{|u|^2},\qquad
a=\frac vB+\lambda b\quad(\lambda\in\mathbb R).
$$

同一已知节点的整个数值历史与该对有相同制备纤维。若另可访问 $\tau=a\cdot b$，两读一次更新恢复 $a=v/B+(\tau/B)b$。

证明。$u\perp b,v=u\times b$ 给 $u\times v=-|u|^2b,|v|^2=|u|^2B$；$v=Ba-Cb$ 给仿射表达式。反向任意非零正交 $u,v$，定义所列 $b,B$，则 $|b|^2=B>0$ 且

$$
b\times v=\frac{(-u\times v)\times v}{|u|^2}=Bu.
$$

取任意 $a=v/B+\lambda b$，得到 $b\times a=u$、$u\times b=v$，所以每个纤维点都实际实现且独立。原始点必有 $\lambda=C/B$，故无遗漏。规范节点尾由首两值的规范递推决定，整个历史相等的反向又包含这两值。依赖制备给 $K=N=0$，全节点历史零。最后 $v\perp b$，所以 $a\cdot b=\lambda B$；供应 $\tau$ 得唯一原制备。

**定理 12.2（精确节点协议的两读下界）。** 在已知 $T_2$、独立未知制备、另可访问 $\tau$、无校准或其它制备档案的合同中，任意确定有限停止的 $\rho$ 单历史协议若至多一次向量 Read，不能恢复全部原制备。两次读一次更新的定理12.1协议达到该读数下界。

证明。限制到 $a=\lambda e_1,b=\mu e_2$、$\lambda,\mu>0$，全族 $\tau=0$。唯一读之前日程没有依赖未知数值的输入，故若有读，其规范时刻 $j\ge2$ 固定。设 Fibonacci 整数 $F_0=0,F_1=1$。由规范叉积递推归纳，$T_j$ 的轴及符号只依 $j$，幅度为

$$
\lambda^{F_{j-1}}\mu^{F_j}.
$$

$j=2$ 的幅度为 $\lambda\mu$，后续两正交轴相乘使幅度相乘，指数按同一 Fibonacci 递推相加。两指数均正。让 $\lambda>0$ 任意变化，取 $\mu=\lambda^{-F_{j-1}/F_j}$，全族同一读数、同一读时刻及 $\tau=0$，原叶对不同。此后的无读更新、后处理与停止都依同一已取得记录，不能分开它们。无读时更不能分开。这个下界量化指定协议中的任意唯一读时刻，不是任意测量函数或较宽校准菜单的原语最小性。

**命题 12.3（依赖节点的档案修复及树身份界限）。** 在依赖分支，$(0,0,\tau)$ 不足：$p=(e_1,e_1)$ 与 $p'=(e_2,e_2)$ 有同一 $\tau=1$ 和全零节点历史。若 $b\ne0$，另存 $b$ 后由 $a=\tau b/B$ 修复；若 $b=0$，须存原 $a$ 或纤维上的其它单射记录。恢复 $p$ 可求值每棵另有代码的树，却不能由数值恢复未知原树；命题6.5的零树身份反例仍成立。

## 13. 同一实现的资源坐标与精确运算边界

**约定 13.1（各目标的同时取得费用）。** 令 $d=\dim V$，主版本 $d=3$，返回完整环境八元数坐标时 $d=7$。下表各行是一条实际历史的共同资源配置。精确实数、整数、多项式和二值记录分别计，源生成、端口供应、合法配对、动作／时间／失败／Stop 身份及输出费用也分别保留。

| 13目标与合同 | 同时读／源更新 | 保留记录与附加权限 | 解码工作与 scratch |
| --- | --- | --- | --- |
| 13初始数值未来：未知树及制备 | 3向量Read、2次 $\rho$ | 初始3向量，即 $3d$ 精确实坐标；源及时间身份；无数量或校准口 | 每次 $G$ 一叉积、一点积、一次准确符号；一临时向量及有限标量 |
| 13当前尾未来：$\mathcal X_1$ | 3尾向量Read、2次 $\rho$ | 取得时3向量；完成后2向量及条件符号 | 一叉积、点积和守卫除法；归档更早初值另计 |
| 13初始联合行为：固定校准 $p$ | 2联合Read、1次 $\rho$；共2向量和2整数回复 | $\nu,u,v$；另有校准及同制备身份 | 整数逆；有限正数幂及校准框架映射；退化分支返回零 |
| 13全参数语义及第一损失恢复 | 另可访问原有限树码；符号递归 | 有限 $z$，或 $\Sigma z$ 加 $\mathcal L$；无数值读取得声明 | 多项式运算／准确整除；次数、系数和代码成本随实际输入，无统一预算 |
| 13原制备：已知 $T_1$ | 2向量Read、1次 $\rho$；另供或早期保留 $\tau$ | $b,K,\tau$ 或恢复的 $a,b$；分支身份 | 有限叉积、范数及 $B\ne0$ 除法；$b=0$ 另存 $a$ |
| 13原制备：已知独立 $T_2$ | 2向量Read、1次 $\rho$；另供 $\tau$ | $u,v,\tau$ 或恢复的 $a,b$ | $|u|^2,B\ne0$ 的有限运算；依赖分支按命题12.3另存档案 |

第一行逐次归档 $x_0$、更新读 $x_1$、更新读 $x_2$，然后停止，当前源为 $\rho^2t$；预测不是把源逆转。若目标保留时刻零，归档的 $x_0$ 不能随滑动窗口删除。尾行只有在第三个读数已提供符号后才可删除它。联合行用两数量回复解码组成，保留初始 $u$；校准可具体存为 $g_1,g_2,g_3,r,s$ 或原 $p$，获取／保存它另计。一个朴素有限幂算法作 $m+n$ 次标量乘法，再作固定维度标架映射；不将其解释为任意实数的有界位复杂度。

**命题 13.2（另授代码时的显式源与算术界）。** 在额外树码权限及逐显式节点求值约定下，$L$ 叶树需 $L-1$ 次叉积，节点数为 $2L-1$；一次 $\rho$ 后至多 $2L$ 叶，$j$ 次后至多 $2^jL$ 叶。求三初始树的向量共至多 $7L-3$ 次叉积。

证明。叶没有叉积、一个节点把两个孩子的叉积数相加再加一，归纳得 $L-1$；节点数同理。每个旧叶一次替换成至多两叶，新生成叶不在同一遍继续替换，所以逐次倍增界成立。三棵树的求值费用至多 $(L-1)+(2L-1)+(4L-1)$。逐节点遍历也能构造其字面替换，输出大小按同一节点数收费。这是明确代码表示的成本，不是黑箱物理 Read 或 $\rho$ 的价格；无代码权限的数值协议仍只使用声明端口。

**约定 13.3（下界、精度与比较范围）。** 定理5.1／命题5.2的最短值针对连续窗口；定理7.2针对固定精确向量对的补充区别；定理11.2针对实际纤维上的附加字母表；命题11.3针对线性记录；定理12.2针对已知节点的确定单读协议；命题8.4针对校准实例的实际联合读／更新。各下界不能换成任意编码、每个制备或物理成本的普遍下界。

所有数值公式使用精确符号、相等判断及非零守卫除法。若表示不供应准确符号／相等，没有从公式自动得到有效分支算法。有限多项式递归因孩子更小而终止；固定数值解码由有限运算构成，但任意实常数的有效表示、位运算误差及输出精度需另给。这里没有噪声律、稳定有限位重建、统计充分性、物理时钟或最优物理预算。

比较须同时固定目标、初始及生成源大小、制备、代码访问、校准、实际联合身份、读种类与宽度、实际更新／graft、实数／整数／多项式／二值档案、解码工作／scratch／输出、精度和控制／失败／Stop 元数据。校准两联合读与无校准三向量读没有所证的全坐标支配关系，不给共同标量价格。组成、原始剪切与条件尾符号分别服务不同目标。

## 14. 来源复用、文献范围与已发表接口的区别

**约定 14.1（原始接口与复用边界）。** 本卷使用以下原始来源，而不把名称相似或线性张成当作恢复权限。

| 14来源 | 承担的原前提与复用范围 |
| --- | --- |
| 14原语法：[Atomic](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§2–5、13；[Continuation](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) §1 | 非空有序树、原 $\rho$、结构解释、$M$ 与数量逆；复用基础，向量节点不换成加法 |
| 14切面：[Boundary Geometry](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) §§5、7、8 | 完整旋转合同与原生可达性分开；固定单位全树标签；八元数二生成切面及外部上下文边界 |
| 14形式源：[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) 及 [Blueprint](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.md) | `FreeMagma Bool`，true对应 $\alpha$、false对应 $\beta$；非空组成纤维、形状与叶位、替换单射；零组成为空 |
| 14上下文：[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)、Continuation13.2 | 全部有限严格上下文、失败与正常零分开、实际联合合法域饱和；本卷固定制备子合同另有直接证明 |
| 14线性观察：Boundary16–17；[ObservableKrylovGrowthBound](../../../D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound.lean)、[MaximalUnobservableSubspace](../../../D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace.lean)、[ObservableKrylovPermanentStability](../../../D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability.lean) | 线性初态、线性更新及线性观察；其维数、加法递推和稳定结论不实例化本卷非线性原树过程 |
| 14Clifford：Atomic355–356 | 结合 Clifford 叶积，356的窗口来自同一原树的连续替换；其六周期和代数逆不移植到叉积或连续变量叶出现 |
| 14已发表原生控制：[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) §44 | 固定单位制备的实际组成／方向像、原生控制及付费单历史取得；本卷直接复用单位机制，额外可变叶制备不由这些控制供应 |
| 14外部仪器：Boundary37–43、Process44.15–44.18 | 所供 $W=E\oplus\mathbb H$ 初态、锚、仪器读／破坏性更新、公共校准，以及仿射或球帽／两半径层来源；不是本卷 $E_p(\rho^jt)$ 的原生变叶过程 |
| 14算术来源估计：Atomic407–413 | Mellin／Abel 来源估计；不授原树制备、复制、逆或校准菜单 |

Process44 已给固定单位制备的方向控制和取得结果，不能将本卷的单位标签、数量逆或相同单位特例另称未发表增量。Boundary43 的两半径初始来源及制备／读取误差合同与本卷额外叶对不同，其误差下界不回答下节的问题。Atomic19、375 的更宽操作或物理接口亦须逐项另外供应。读取既有 D5 原文只是复用接口，本卷不新增或声称运行其 Lean 核验。

**约定 14.2（主要文献与所用数学）。** 经典基础为 `literature-attested`：Erik Darpö, *Vector product algebras*, [arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，Lemma2及证明，*Bull. London Math. Soc.* 41(5), 898–902，[DOI](https://doi.org/10.1112/blms/bdp066)，其交替积、非退化对称型、循环配对与范数条件在本卷取正定实情形。John C. Baez, *The Octonions*, *Bull. Amer. Math. Soc.* 39, 145–205，[DOI](https://doi.org/10.1090/S0273-0979-01-00934-X)，作者原文 [预备定义与交替性](https://math.ucr.edu/home/baez/octonions/node2.html) 和 [叉积／$G_2$](https://math.ucr.edu/home/baez/octonions/node14.html) 支持实八元数及二生成切面；不支持完整 $SO(7)$ 控制。所需重复向量公式已在引理2.2直接证明。

Soledad Villar 等，*Scalars are universal: Equivariant machine learning, structured like classical physics*, [arXiv:2106.06610v2](https://arxiv.org/pdf/2106.06610v2)，Proposition5及AppendixB，为经典多项式等变 Gram 系数表示的背景；本卷只需两输入三维情形，并直接证明其特定树递归和唯一性，不据一般等变形式推定实际像。Mihály Petreczky、Laurent Bako、Jan H. van Schuppen，*Realization theory of discrete-time linear switched systems*, [arXiv:1103.1343v2](https://arxiv.org/pdf/1103.1343v2)，Remark6说明响应表可能需要不同切换实验；其线性实现定理未用作本卷前提，也不供应单历史中的反事实重播。

本卷全树符号恢复、实际尾像、校准联合边界和已知节点取得是上述准确源合同下的仓内综合推导（`repo-derived`）。普通证明与实际反例承担结论，不作全球原创性或穷尽检索声明。J. C. Turner, *On Vector Sequence Recurrence Equations in Fibonacci Vector Geometry*, [DOI](https://doi.org/10.1007/978-94-011-4271-7_32) 的完整原文假设尚未取得；它只是未核查线索，不充当前提或新颖性证据。

## 15. 有限核验的证据界与未解稳定性

**约定 15.1（精确核验的作用）。** 有限核验可检查树枚举、原括号求值、运输、归约、窗口公式及指定反例；全称结论由前文结构归纳、唯一性与单射证明承担。有限样本不证明无限全树或任意制备的命题，也不取代真实联合像的反向构造、读协议下界或所供实数的有效表示。没有据样本建立物理读／控制、有限位精度或稳定性结论。

整数及有理数核验枚举了1–7叶的全部20,134棵有序树，在10个正交、非正交、依赖或零叶制备上核对时刻0–5的三读公式及尾关系；字面替换运输另核对1–4叶的102棵树及0–3次替换。符号核验枚举1–6叶的3,238棵树，核对 $H\Sigma=\Theta H$、剩余反演及第1–3次替换的相同碰撞类。命题5.2、8.4的有理反例和命题8.5在 $\mathbb Q(\sqrt{31})$ 中的同树反例逐坐标准确成立；网格 $\{-1,0,1\}^3$ 中192个非零有序正交对核对了定理7.2的两个实际见证及制备／节点逆式。这些范围之外的全称结论仍由各条普通证明承担。

**开放问题 15.2（无界树大小下的实际三读稳定性）。** 固定 $L,H>0$ 与 $0<\delta_0<L^4$。仅取实际树／制备满足

$$
|a|,|b|\le L,\qquad \Delta\ge\delta_0,\qquad
|x_0|,|x_1|,|x_2|\le H.
$$

对两实际来源都满足这些限制且 $\max_{0\le j\le2}|x_j-x'_j|\le\varepsilon$，定义

$$
\omega(\varepsilon)=\sup|x_3-x'_3|,
$$

空上确界约定为零。树大小无界时，是否 $\omega(\varepsilon)\to0$？若成立，尖锐阶是什么；若不成立，哪组实际成对树／制备见证障碍？这项稳定性问题保持实际 $W_3$ 像及共同来源条件，不能以环境符号函数的跳变替代反例。它尚未由本卷的精确恢复、有限核验或其它仪器的误差合同解决。

## 追加锚（本行以下为增补区）

## 16. 实际来源的投影约束与无界树稳定域

本节至第23节回答开放问题15.2的指定下一向量任务；其原文保留。来源、括号、定向叉积和唯一实际更新仍为定义1.1–1.2，制备在执行过程中固定。定理3.1、引理4.2、定理4.3及5.1分别供应运输、五符号描述子、实际尾幅度与精确预测；这些已建立的接口不重复计作稳定性结果。以下主结论只取三维版本。

**定义 16.1（主域、记录距离与目标模量）。** 固定实数 $L,H>0$、$0<d_0<L^4$；$d_0$ 对应开放问题15.2的 $\delta_0$。记

$$
\mathcal D_{L,H,d_0}=\{(t,p)\in\mathcal T\times(\mathbb R^3)^2:
|a|,|b|\le L,\ \Delta\ge d_0,\ |x_j|\le H\ (0\le j\le2)\}.
$$

树可为任意非空有限有序树，大小无统一上限。置 $q_j=|x_j|$、$w=x_2\times x_1$，两记录间使用

$$
d(W_3,W'_3)=\max_{0\le j\le2}|x_j-x'_j|,\qquad
\omega(\varepsilon)=\sup_{\substack{(t,p),(t',p')\in\mathcal D_{L,H,d_0}\\
d(W_3,W'_3)\le\varepsilon}}|x_3-x'_3|.
$$

空上确界取零。两成员分别满足全部联合限制，树和制备都可不同。该域非空：取垂直叶长 $d_0^{1/4}<L$，零 cherry 的整个响应为零；包含零子树的更大树也供应任意大来源。本任务只预测 $x_3$，不把目标换成原语法、原制备或全时间误差。

为避免标量界 $L$ 与约定2.1的向量 $L$ 混淆，以下记

$$
U=K\times a=Ca-Ab,\qquad V=K\times b=Ba-Cb.
$$

它们分别就是前文的向量 $L,N$；$A,B,C,\Delta,K,F$ 含义不变。计数、正交化、缩放与旋转仅为证明中构造实际竞争源的方法，不供应数量、语法、校准、逆、复制、复位、归一化、旋转或重制备的观察／动作端口。

**引理 16.2（投影同时控制角度与幅度）。** 设 $\Delta>0$ 且 $\chi(t)=\sigma f_i\ne0$。令 $u=w/|w|$，则

$$
P:=\sigma x_0\cdot u>0,\qquad
P\ge\frac{q_2}{q_1},\qquad
P\ge\sqrt{\frac{\Delta}{AB}}\,q_0.
$$

证明。定理4.3的尾标架给

$$
x_1=\sigma r^ms^ng_i,\qquad
x_2=\sigma r^ns^{m+n}g_{i+1},\qquad
w=q_1q_2g_{i+2},\quad r=\sqrt B,\ s=\sqrt\Delta.
$$

由引理4.2，非零标签的所选描述子没有 $C$ 因子，可将 $\sigma$ 提出，并选初值符号 $Z\in\{a,b,K,-U,V\}$，使 $x_0=\sigma A^iB^j\Delta^kZ$。这里 $i,j,k$ 为描述子指数，而非标签索引。赋予 $A,B,C,\Delta$ 双次数 $(2,0),(0,2),(1,1),(2,2)$，赋予 $a,b,K,U,V$ 双次数 $(1,0),(0,1),(1,1),(2,1),(1,2)$。完整表的每一项都保持孩子双次数的和；故对 $Z$ 的次数 $(m_Z,n_Z)$ 有

$$
m=2i+2k+m_Z,\qquad n=2j+2k+n_Z.
$$

对应正向投影如下；各行的 $u$ 是该符号实际所属尾分支的 $g_{i+2}$。

| 16初值符号 $Z$ | $Z\cdot u$ | $(Z\cdot u)/|Z|$ |
| --- | --- | --- |
| 16投影 $a$ | $s/r$ | $\sqrt{\Delta/(AB)}$ |
| 16投影 $b$ | $r$ | $1$ |
| 16投影 $K$ | $s$ | $1$ |
| 16投影 $-U$ | $s^2/r$ | $\sqrt{\Delta/(AB)}$ |
| 16投影 $V$ | $rs$ | $1$ |

例如 $a\cdot V=\Delta$、$(-U)\cdot b=\Delta$，而 $|U|^2=A\Delta,|V|^2=B\Delta$，给两个非平凡比值。各投影又恰等于 $(s/r)^{m_Z}r^{n_Z}$。利用 $A=(\Delta/B)(AB/\Delta)$ 得完整恒等式

$$
P=\left(\frac{AB}{\Delta}\right)^i(s/r)^mr^n
=\left(\frac{AB}{\Delta}\right)^i\frac{q_2}{q_1}.
$$

$AB/\Delta\ge1$ 给幅度不等式；投影／范数比值中正单项式相消，给角度不等式。所有所除量在本分支严格为正。

**推论 16.3（实际三读的统一定量关系）。** 对任意制备与树，

$$
|x_0\cdot w|\ge q_2^2,\qquad q_2\le q_0q_1.
$$

在主域上置 $c=\sqrt{d_0}/L^2\in(0,1)$，还同时有

$$
|x_0\cdot w|\ge c q_0|w|,\qquad |w|\le H^2q_0,
\qquad |x_3|=|w|\le H^2.
$$

证明。规则分支中 $|w|=q_1q_2$，将引理16.2第一界乘以此量得到第一式；$P\le q_0$ 给第二式。主域的 $AB\le L^4,\Delta\ge d_0$ 给角度下界 $c$，并由 $q_1\le H$ 得 $|w|=q_1q_2\le q_0q_1^2\le H^2q_0$。定理5.1给最后等式。零标签的 $x_1,x_2,x_3$ 全零；依赖制备的 $x_2,x_3$ 全零，故这些分支也满足不含除法的全部结论。这里没有假设某一读数或三重积有统一严格正下界。

环境三元组 $x_0=\pm\varepsilon e_3,x_1=e_1,x_2=e_2$ 在 $\varepsilon<1$ 时违反 $q_2\le q_0q_1$。因此，环境符号公式在这些点的跳变不能当作实际来源的不稳定见证。

## 17. 全树下一输出的线性模量与实际尖锐对

**定理 17.1（变化制备的统一线性界）。** 对定义16.1的每组参数及每个 $\varepsilon\ge0$，

$$
0\le\omega(\varepsilon)\le
\min\{2H^2,K_*\varepsilon\},\qquad
K_*=2H+\frac{2H^2+4H}{c}.
$$

因此开放问题15.2所问的 $\omega(\varepsilon)\to0$ 对全部允许参数成立；此处的系数是充分界，不是最优系数。

证明。取任意实际对，令 $e=d(W_3,W'_3)$、$\delta_w=|w-w'|$。两成员的读数范数界及双线性给

$$
\delta_w\le|x_2-x'_2|\,|x_1|+|x'_2|\,|x_1-x'_1|\le2He.
$$

若任一 $w$ 为零，或两非零分支的实际符号相同，定理5.1给目标差至多 $\delta_w$。余下两符号相反且 $q_0,q'_0>0$；交换成员名使 $q_0\ge q'_0$。三重积异号及推论16.3给

$$
cq_0|w|\le|x_0\cdot w-x'_0\cdot w'|
\le e|w|+q'_0\delta_w.
$$

除以 $q_0$，用 $|w|/q_0\le H^2,q'_0/q_0\le1$，得

$$
|w|\le\frac{H^2e+\delta_w}{c},\qquad
|x_3-x'_3|=|w+w'|\le2|w|+\delta_w\le K_*e.
$$

此论证覆盖 $e=0$ 及全部符号、零分支。两目标范数又各不超过 $H^2$；取实际对的上确界得到所列两界，不需要紧性、有限树截断或固定制备。

**定理 17.2（非零目标的实际线性下界）。** 若主域含一个 $x_3\ne0$ 的来源，则 $\omega(\varepsilon)=\Theta(\varepsilon)$ 当 $\varepsilon\downarrow0$；若不含，则 $\omega\equiv0$。

证明。固定该来源，令 $v=|x_3|>0$、$M_0=\max(q_0,q_1,q_2)>0$。取垂直于 $x_3$ 的旋转轴，以正向旋转 $Q_\theta$ 同时旋转两个原叶，保留同一字面树。定向体积给 $Q(u\times v)=(Qu)\times(Qv)$，结构归纳得 $x'_j=Q_\theta x_j$。两制备的 Gram 数据、叶范数及三个读数范数完全相同，故包括等号在内的全部限制同时保留。旋转差满足

$$
|Q_\theta z-z|\le2|z|\sin(\theta/2),
$$

当 $z$ 垂直于轴时等号成立。对 $0<\varepsilon\le2M_0$ 选 $2\sin(\theta/2)=\varepsilon/M_0$，则三读差都至多 $\varepsilon$，目标差恰为 $(v/M_0)\varepsilon$。结合定理17.1得尖锐阶。若全域目标为零，定义直接给零模量。旋转构造的是两个合法所供制备，未授予内部观察者旋转动作。固定 $p$ 的子域继承上界，却不能直接继承本变化制备下界。

## 18. 非零预测的实际可行性与达到／未达到的阈值

**定义 18.1（统一参数与组成支撑）。** 置

$$
\varphi=\frac{1+\sqrt5}{2},\quad s_0=\sqrt{d_0},\quad
z=\log s_0,\quad \ell=\log L,\quad h=\log H,\quad
\gamma=z-\ell/\varphi^2,\quad T=s_0^{\varphi^2}/L=e^{\varphi^2\gamma}.
$$

站立条件为 $z<2\ell$。非零单位标签的组成支撑恰为

$$
\mathcal S=\{(1,0),(0,1)\}\cup
\{(m,n):m,n\ge1,\ (m,n)\notin(2\mathbb N)^2\}.
$$

此支撑直接复用 [Process Geometry 定理44.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)：三轴的 $\mathbb F_2^2$ 分次排除双偶混合组成，纯标签多叶树的同标签 cherry 排除其非零值。可用的实际见证是从 $\langle\beta,\alpha\rangle$ 出发，两次左接同一标签来增加对应叶数2；正奇／奇组成由此全得到。正偶／奇再左接一次 $\alpha$，正奇／偶再左接一次 $\beta$，所接轴与原轴垂直，仍非零。另两纯组成就是原叶。这些是构造来源的有限配方，不是观察者取得组成或接合权限。

**定理 18.2（全实际像上的三线可行性判据）。** 主域含非零 $x_3$，当且仅当存在 $(m,n)\in\mathcal S$ 及 $v\in[z-\ell,\ell]$，使

$$
\begin{aligned}
f_0(v)&=mz+(n-m)v\le h,\\
f_1(v)&=nz+mv\le h,\\
f_2(v)&=(m+n)z+nv=f_0(v)+f_1(v)\le h.
\end{aligned}
$$

证明。任一非零目标来源有 $\Delta>0$ 和非零标签。将 $a$ 换为 $a_\perp=a-(C/B)b=V/B$：它与 $b$ 垂直，范数不增加，$B,\Delta,F(p)$ 不变，故全部尾值不变。正交齐次性给新初值范数

$$
|E_{(a_\perp,b)}(t)|=(s/r)^mr^n=q_2/q_1\le q_0
$$

（引理16.2）。再同时缩放两垂直叶，比例 $(d_0/\Delta)^{1/4}\le1$。每个 $\rho^jt$ 有正的有限叶数，其求值按这个比例的叶数次幂缩放，故叶界与三读界都保留，行列式成为 $d_0$，且非零仍非零。这证明全部原来源的存在性可归约到正交、恰取最小行列式的实际制备，而非环境三元组。

这样的叶长必可写为 $|b|=e^v,|a|=s_0e^{-v}$；两叶界恰给 $z-\ell\le v\le\ell$。正交齐次性及组成更新给

$$
q_0=s_0^me^{(n-m)v},\quad
q_1=s_0^ne^{mv},\quad
q_2=s_0^{m+n}e^{nv}=q_0q_1.
$$

取对数即得必要性。反向，为所选支撑组成取定义18.1的字面树，再供应 $(s_0e^{-v}e_1,e^ve_2)$。所列幅度是同一实际来源的三个读数，叶界、行列式和三个不等式同时成立，尾非零。故判据充分且覆盖全部树大小。

**定理 18.3（完整零／非零制度）。** 在站立条件下，下表准确决定定理17.2的非零线性分支；不满足右栏条件时目标全零且 $\omega\equiv0$。

| 18参数制度 | 主域存在非零预测的充要条件 |
| --- | --- |
| 18收缩 $\gamma<0$，即 $d_0<L^{2/\varphi^2}$ | 每个 $H>0$ |
| 18临界 $\gamma=0$，即 $d_0=L^{2/\varphi^2}$ | 恰为 $H>1$，不包含等号 |
| 18非收缩 $\gamma>0$，即 $d_0>L^{2/\varphi^2}$ | 恰为 $H\ge H_*>1$，$H_*$ 由定理18.4给出并达到 |

临界和非收缩制度均强迫 $L>1,s_0>1$。

证明。先取实际端点制备 $a=Le_1,b=(s_0/L)e_2$，及规范实际树 $T_j=\rho^j\alpha$。命题5.3的原结构递推给垂直循环方向及正幅度

$$
Q_0=L,\quad Q_1=s_0/L,\quad Q_{j+2}=Q_{j+1}Q_j.
$$

以 $F_0=0,F_1=1,F_{j+1}=F_j+F_{j-1}$ 记 Fibonacci 数，则对 $j\ge1$，

$$
\log Q_j=F_{j-1}\ell+F_j(z-\ell)
=\frac{\varphi^j}{\sqrt5}\gamma+O(\varphi^{-j}).
$$

这里复用的闭式 $F_j=(\varphi^j-(-\varphi^{-1})^j)/\sqrt5$ 由两个初值与同一递推验证。$\gamma<0$ 时三个连续幅度都趋于零，任意 $H>0$ 都由某个有限 $T_j$ 实现；包括 $L\le1$ 或 $s_0\le1$ 的情况。$\gamma=0$ 时 $z=\ell/\varphi^2<2\ell$ 强迫 $\ell,z>0$，准确有 $\log Q_j=\ell(-\varphi^{-1})^j\to0$，故所有 $H>1$ 可行。

为排除临界 $H\le1$，对定理18.2的任意组成及允许 $v$，计算

$$
f_0+\varphi f_1=(m+\varphi n)(z+v/\varphi)
\ge\varphi\gamma(m+\varphi n).
$$

临界时右侧零。若 $h<0$，前两线均至多 $h$ 与此矛盾。若 $h=0$，两线必须同时为零；将其视为关于两叶对数的线性方程，其行列式为 $m^2+mn-n^2\ne0$。非空整数组成不可能给零：零坐标情形直接成立，其余会使有理比值成为 $X^2+X-1=0$ 的无理根。因此两叶对数都零，与两者和 $z>0$ 矛盾。这证明临界下确界1未达到。非收缩部分由下一定理给出。

最后，若 $\ell\le0$，$z<2\ell\le\ell/\varphi^2$，必有 $\gamma<0$；若 $\ell>0,z\le0$ 也必收缩。故余下制度的 $\ell,z$ 均正。

**定理 18.4（非收缩制度的有限达到阈值）。** 若 $\gamma>0$，定义

$$
\begin{gathered}
g_{mn}=\min_{v\in[z-\ell,\ell]}\max\{f_0(v),f_1(v),f_2(v)\},\\
\mathcal F=\{(m,n)\in\mathcal S:m+\varphi n\le\varphi z/\gamma\},\\
h_*=\min_{(m,n)\in\mathcal F}g_{mn},\qquad H_*=e^{h_*}.
\end{gathered}
$$

这是非空有限优化，$0<h_*\le z$。每项 $g_{mn}$ 只须在区间两端及落在区间中的下列已定义交点取最大值再比较：

$$
\frac{(n-m)z}{n-2m},\qquad -\frac{nz}{m},\qquad
-\frac{mz}{n-m}.
$$

零分母项略去。某个实际有限树及允许制备在 $H=H_*$ 同时满足全部界，并有非零预测。

证明。定理18.3证明中的加权式及 $f_0,f_1\le\max f_j$ 给

$$
g_{mn}\ge\gamma(m+\varphi n)/\varphi>0.
$$

$\alpha$ 来源在两叶同长 $\sqrt{s_0}<L$ 时三幅度为 $\sqrt{s_0},\sqrt{s_0},s_0$，其最大对数恰为 $z>0$。任一能与该值持平或改善的组成必在 $\mathcal F$；被略去的组成的最大对数严格大于 $z$，不能改变全局下确界。$\mathcal F$ 有限且含 $\alpha$，每个闭区间上的连续函数都达到最小值，故全局最小正且达到。三条仿射线的凸分段线性最大值，在端点、线交点或常值线段处达到最小；常值线段的端点也给同值。上式恰为三种两两交点，平行或重合不增加候选。这证明有限求值公式。用定理18.2的实际组成见证和优化制备实现最小值，得到 $H\ge H_*$ 的充分性；同一判据给必要性，包括等号。

有限集只服务存在性／阈值计算，不给主模量定理添加树大小上限；任意大零树和任意实际规则树都仍在相应全称域内。

## 19. 有限判据的覆盖证明与端点简化

**命题 19.1（测试给定读数界的两种有限截止）。** 在 $\gamma>0$ 时，若 $h\le0$ 则无非零预测；若 $h>0$，定理18.2的完整三线判据可仅测试

$$
(m,n)\in\mathcal S,\qquad m+\varphi n\le h/\gamma.
$$

较宽截止 $m+\varphi n\le\varphi h/\gamma$ 也给准确决定。它们是不同的有限列表，但连同相同三线判据，均成功当且仅当 $h\ge h_*$。

证明。即使不作正交化，定理4.3给规则尾

$$
q_1q_2^{\varphi}=(rs^{\varphi})^{m+\varphi n},\qquad
rs^{\varphi}\ge s^{\varphi^2}/L\ge T.
$$

因 $\Delta\le AB\le L^2B$，有 $r\ge s/L$；$s\ge s_0$ 给第二个界。由 $q_1,q_2\le H$ 及 $\log T=\varphi^2\gamma$，得到 $(m+\varphi n)\gamma\le h$。这是较小列表的必要截止。较宽列表来自 $f_0+\varphi f_1\ge\varphi\gamma(m+\varphi n)$ 及 $f_0,f_1\le h$。两列表都覆盖每个可行组成，测试内的三线不等式又各自充分，故完整决定等价。若以 Gram 平方量写参数 $\log d_0,2\log L,2\log H,\log B$，分别是 $2z,2\ell,2h,2v$，不得把这项倍数变化与截止的 $\varphi$ 因子混为一谈。

**定理 19.2（端点制度的准确有限公式）。** 若 $s_0\le1$，站立条件强迫 $\gamma<0$，任意 $H>0$ 可行。若 $s_0>1$，令

$$
\eta=\ell/z-1>-1/2.
$$

非零预测的充要条件还可写为

| 19端点参数 | 准确条件 |
| --- | --- |
| 19叶阈值 $\eta\le1$，即 $L\le s_0^2$ | $H\ge s_0$ |
| 19有限中间区 $1<\eta<\varphi$ | $H\ge s_0^{\psi(\eta)}$ |
| 19临界端点 $\eta=\varphi$，即 $L=s_0^{\varphi^2}$ | $H>1$ |
| 19收缩端点 $\eta>\varphi$ | 每个 $H>0$ |

中间区置

$$
\begin{gathered}
G_\eta(m,n)=\max\{(1+\eta)m-\eta n,\ n-\eta m,\ m+(1-\eta)n\},\\
B_\eta=\frac{\eta+1}{\eta+1-\eta^2},\\
\mathcal E_\eta=\{(m,n):1\le m\le\lfloor B_\eta\rfloor,
\ m<n\le\lfloor\eta m+1\rfloor,\ (m,n)\notin(2\mathbb N)^2\},\\
\psi(\eta)=\min\bigl(\{1\}\cup
\{G_\eta(m,n):(m,n)\in\mathcal E_\eta\}\bigr)>0.
\end{gathered}
$$

证明。$s_0\le1$ 时，若 $\ell>0$ 直接有 $\gamma<0$；若 $\ell\le0$，则 $z<2\ell\le\ell/\varphi^2$，仍收缩。以下取 $z>0$。纯组成中 $\alpha$ 的 $f_2=z$、$\beta$ 的 $f_1=z$，不能低于叶阈值；$\alpha$ 在等叶长处达到它。对混合 $n\le m$，若 $v<0$，则 $f_0\ge mz\ge z$；若 $v\ge0$，则 $f_2\ge(m+n)z\ge2z$。故任何改善必须有 $n>m\ge1$。此时三线关于 $v$ 的斜率均正，其最优点为 $v=z-\ell=-\eta z$，由实际端点制备 $a=Le_1,b=(s_0/L)e_2$ 实现；该点最大对数除以 $z$ 恰为 $G_\eta$。

当 $\eta\le1$，第三项 $m+(1-\eta)n\ge m\ge1$，不能改善叶阈值，得第一行。当 $1<\eta<\varphi$，任何可与叶持平或改善的组成须有 $G_\eta\le1$，由前两项得到

$$
\frac{(1+\eta)m-1}{\eta}\le n\le\eta m+1,\qquad
(\eta+1-\eta^2)m\le\eta+1.
$$

这证明有限集 $\mathcal E_\eta$ 覆盖全部可能优化者；略去的组成的指数严格大于1。前两项不能同时非正，否则会有 $1+1/\eta\le n/m\le\eta$，与 $\eta^2<\eta+1$ 矛盾。因此有限最小值正，且每个所留组成有实际树及端点制备，阈值达到。

当 $\eta=\varphi$，令 $e=n-\varphi m$，端点三项为 $-\varphi e,e,-e/\varphi$；整数组成及无理性给 $e\ne0$，最大值严格正。连续 Fibonacci 组成 $(F_j,F_{j+1})$ 的 $e=(-1)^j\varphi^{-j}\to0$，相邻数互素、不会双偶，故均在支撑内。其最大指数趋于零但不达到，正是定理18.3的临界制度。若 $\eta>\varphi$，选择有理比值 $1+1/\eta<n/m<\eta$，约成互素正整数后取任意大奇数倍。支撑仍非双偶，前两项负；第三项是前两项的和，也负。其倍数趋向负无穷，证明任意 $H>0$ 可行。

**命题 19.3（其它有限列表与同一阈值）。** 在 $1<\eta<\varphi$，也可用全部支持的 $n>m\ge1$ 且

$$
m+n\le\frac{\varphi^3}{\varphi-\eta}
$$

计算 $\min(\{1\}\cup\{G_\eta\})$；或使用较小加权列表 $m+\varphi n\le\varphi^3/(\varphi-\eta)$。两者均给 $\psi(\eta)$，与定理18.4的区间优化相同。

证明。令 $a_0=(1+\eta)m-\eta n,b_0=n-\eta m$，则

$$
a_0+\varphi b_0=(\varphi-\eta)(n+m/\varphi),\qquad
G_\eta\ge\frac{(\varphi-\eta)(m+\varphi n)}{\varphi^3}
\ge\frac{(\varphi-\eta)(m+n)}{\varphi^3}.
$$

超出任何所列截止的组成的最大值大于1，不能改善或持平。另一方面 $\gamma=z(\varphi-\eta)/\varphi^2$，故加权截止恰是定理18.4的 $\mathcal F$ 截止。纯组成及 $n\le m$ 已由定理19.2排除改善，$n>m$ 的区间最小值确在端点，故两个优化相同。较宽列表不意味着其每个组成都可行；必须仍计算完整最大值。

**例 19.4（非平滑阈值与零目标的非零初值）。** 精确公式给

$$
\psi(5/4)=3/4,\quad\psi(3/2)=1/2,\quad
\psi(8/5)=1/5,\quad\psi(21/13)=1/13.
$$

前两值可直接检查各自 $\mathcal E_\eta$：$m$ 分别至多3及10；$\eta=5/4$ 的列表是 $(1,2),(2,3),(3,4)$，最大指数分别为 $3/4,5/4,2$；若 $\eta=3/2$，正的 $G_\eta$ 是半整数，$(1,2)$ 达到 $1/2$。后两值无需更大枚举：正的 $G_{8/5},G_{21/13}$ 分别为 $1/5,1/13$ 的整数倍，组成 $(3,5),(8,13)$ 分别给三项 $(-1/5,1/5,0),(-1/13,1/13,0)$。它们都在实际支撑中，因此达到对应下界。例如 $\eta=8/5$ 的同源三范数为 $(s_0^{-1/5},s_0^{1/5},1)$。$L=2,d_0=4$ 给 $\eta=0,H_*=2$。

零目标制度不意味着初值也零。对任意站立参数，取

$$
a=Le_1,\qquad b=\xi e_1+(\sqrt{d_0}/L)e_2,
$$

其中 $0<\xi<\sqrt{L^2-d_0/L^2}$ 且 $L\xi\sqrt{d_0}\le H$；这样的小 $\xi$ 总存在。命题5.3的实际树 $\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle$ 有初值 $CK\ne0$，范数 $L\xi\sqrt{d_0}$，零标签及全零尾，且两叶界与 $\Delta=d_0$ 同时成立。

这些判据是数学实参数的精确存在性决定；未知实数的相等或整数截止的有限位有效决定仍需表示合同。证明中的组成搜索不成为内部观察者的数量端口。

## 20. 同一破坏性历史的有限精度取得、恢复风险与位成本

**定义 20.1（联合有界误差取得合同）。** 对一个未知 $(t,p)\in\mathcal D_{L,H,d_0}$ 执行

$$
\operatorname{Read},\rho,\operatorname{Read},\rho,
\operatorname{Read},\operatorname{Stop}.
$$

这是三次付费完整向量回复、两次破坏性原更新的一条实际历史，停止时当前源为 $\rho^2t$。另供应同时误差承诺

$$
|y_j-x_j|\le\delta\qquad(0\le j\le2),\quad\delta\ge0.
$$

制备和动作仍准确。三个误差可联合对抗、相关及依赖历史，不假设独立抽样、复读、平均、噪声分布或重播。回复不必是任何精确实际 $W_3$。公共界只是制备／仪器供应者承担的域与精度承诺，不是读出原 $a,b$ 的校准。

**定理 20.2（无需额外端口的显式恢复器）。** 计算

$$
\widetilde w=y_2\times y_1,\qquad
\widehat x_3=\operatorname{sgn}(y_0\cdot\widetilde w)\widetilde w,
\quad\operatorname{sgn}(0)=0.
$$

对每个允许实际来源和误差三元组，

$$
|\widehat x_3-x_3|\le\frac4c(H^2+2H+\delta)\delta.
$$

特别在 $\delta\le1$ 时，$C_{\rm err}=4(H^2+2H+1)/c$ 是充分线性系数。恢复器本身不读取公共参数、组成、树码、校准或附加符号，也不作归一化、除法或源更新。

证明。展开带误差叉积给

$$
|\widetilde w-w|\le b_\delta:=(2H+\delta)\delta.
$$

若 $w=0$，或计算符号与实际非零符号相同，目标误差至多 $b_\delta$。若符号错误或计算符号为零，目标误差至多 $2|w|+b_\delta$。令 $u_0=|x_0|$。若 $u_0<2\delta$，推论16.3给此误差至多 $4H^2\delta+b_\delta$，不超过所述界。若 $u_0\ge2\delta>0$，两标量异号或计算值为零，故

$$
\begin{aligned}
cu_0|w|&\le|x_0\cdot w-y_0\cdot\widetilde w|\\
&\le\delta|w|+(u_0+\delta)b_\delta
\le H^2u_0\delta+\tfrac32u_0b_\delta.
\end{aligned}
$$

因此误差至多 $2H^2\delta/c+(3/c+1)b_\delta\le(4/c)(H^2\delta+b_\delta)$，恰为所述界。$c<1$ 保证上述常数比较。$\delta=0$ 时定理5.1给准确结果，含全部零分支。错误符号的幅度由实际来源约束控制，而非由仪器免费供应符号裕量。

**推论 20.3（固定三读的准确风险阶与抽象选择边界）。** 假设除这三个回复及相同日程／Stop 元数据外，没有精确来源、语法、制备或时间费用侧信道；误差允许定义20.1的完整三个乘积球。令

$$
R_\delta=\inf_{R:((\mathbb R^3)^3)\to\mathbb R^3}
\sup_{\substack{(t,p)\in\mathcal D_{L,H,d_0}\\|y_j-x_j|\le\delta}}
|R(y)-x_3|.
$$

这里允许全部集合函数，不附有效性、可测性或连续性约束。复用 [Recovery Geometry 定义3.1及定理3.2](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 的候选纤维原则，得到

$$
\frac12\omega(2\delta)\le R_\delta\le\omega(2\delta).
$$

非零制度的固定记录对抗风险为 $\Theta(\delta)$；全零目标制度的类感知常零恢复器风险零，并可免去专为 $x_3$ 的取得。通用带噪公式本身在后一制度不必输出零。

证明与接口对应。取 $X=\mathcal D_{L,H,d_0}$、数据空间 $Y=(\mathbb R^3)^3$、合法中心空间 $S=\mathbb R^3$、目标 $F(t,p)=x_3$，噪声关系就是定义20.1。任意距离至多 $2\delta$ 的两实际记录都可产生同一逐分量中点回复，任一共同输出至少在一端误差为目标差的一半。取上确界给下界，即使上确界未达到也成立。上界可为每个非空兼容来源纤维选一个实际来源并输出其目标；同一数据的其它兼容记录距它至多 $2\delta$，故误差至多 $\omega(2\delta)$，空纤维可输出零。该选择是集合函数存在，不是有限来源搜索。定理20.2另给无需选择的有限运算上界。定理17.2的实际旋转对给非零制度的反向阶。

这仅是该固定记录及完整误差关系的下界；更丰富付费协议或某个确定量化器，未必允许中点回复，不能自动继承它。

**命题 20.4（离开实际像的 Lipschitz 延拓存在）。** 令 $\mathcal A=W_3(\mathcal D_{L,H,d_0})$，则 $x_3=f(W_3)$ 在 $\mathcal A$ 上良定义且 $K_*$-Lipschitz。它有到全部 $(\mathbb R^3)^3$ 的向量延拓，常数至多 $\sqrt3K_*$；此存在性不供应有限求值器或像外数据的实际来源身份。

证明。定理5.1给良定义，定理17.1给 Lipschitz。对每个输出坐标 $i$ 使用 McShane 标量延拓（文献见约定23.1）：

$$
\overline f_i(y)=\sup_{z'\in\mathcal A}
\{f_i(z')-K_*d(y,z')\}.
$$

固定一个 $z_0\in\mathcal A$，三角不等式和像内 Lipschitz 给被取上确界的每项至多 $f_i(z_0)+K_*d(y,z_0)$；$z'=z_0$ 又给有限下界，故值有限。若 $y\in\mathcal A$，像内不等式使每项至多 $f_i(y)$，$z'=y$ 达到等号。各项关于 $y$ 的 Lipschitz 常数为 $K_*$，取上确界仍保持，三个坐标的 Euclidean 组合给 $\sqrt3K_*$。本证明不需要像闭合、紧性或有限树集。无限上确界和抽象纤维选择各有自己的实现义务；取得与位成本由下一命题的直接公式承担。

**命题 20.5（dyadic 回复的有限整数解码）。** 若仪器实际供应

$$
y_{jk}=n_{jk}2^{-b},\quad n_{jk}\in\mathbb Z,\quad b\in\mathbb N,
$$

并保证定义20.1的同时误差，则定理20.2可由固定次数整数乘加与整数符号比较实现，准确包含计算结果为零的分支。最近坐标舍入本身的 Euclidean 向量误差至多 $\sqrt3\,2^{-b-1}$；若另有传感误差，其与量化误差用三角不等式明确合成总 $\delta$。

证明与共同资源。$\delta\le1$ 时 $|y_{jk}|\le H+1$，九个分子各需 $O(1+b+\log(1+H))$ 位，记此宽度为 $B_{\rm num}$。叉积公共分母为 $2^{2b}$，点积公共分母为 $2^{3b}$，正分母不影响符号。用整数准确计算两者，返回带该符号的 dyadic 叉积，不需要未表示实数的符号 oracle。最终再舍入输出时，其向量误差 $\xi_{\rm out}$ 加到定理20.2右侧。

同一实现保留九个 $O(B_{\rm num})$ 位数值字，另保留付费的动作／读数／时间／Stop／源版本身份与 live 源句柄。固定数量的 $O(B_{\rm num})$ 位临时字和三个输出字足够；中间乘积宽度只是输入宽度的固定倍数。学校乘法及加法给 $O(B_{\rm num}^2)$ 位工作、$O(B_{\rm num})$ 临时位。三个先后回复必须按实际历史取得与保留，树／组成／语法寄存器不在合同中。

有效选择输出容差，还需可用的保守公共界 $\overline H\ge H$、$0<\overline c\le c$；选择 $b$ 使总 $\delta\le1$ 且

$$
\frac{4(\overline H^2+2\overline H+1)}{\overline c}\delta
+\xi_{\rm out}
$$

不超过所求容差。单有数学实常数不供应这一计算表示。这些是取得后的保留／解码／输出成本，不给制备或界的认证、物理有限位 Read、准确 $\rho$ 执行、隐藏树存储及无界树求值定价；显式树码另供时才适用命题13.2的逐节点成本。近似动作或制备误差需另建合同，不能挤进纯读数误差。

若一个另外声明的随机模型保证同时事件 $|y_j-x_j|\le\delta$ 的概率至少 $1-\alpha$，则上述逐路径结论在该事件上成立，因而具有该概率保证。独立性、集中估计、分布风险和复读平均收益均不从此推出。当前有限整数解码已给同域线性误差阶与位阶；引入公共参数、守卫和有理除法的截断／裁剪公式不构成这里已证明的取得或资源改进，常数最优性及另求恢复器连续性的任务仍分别保留。

## 21. 仅有三读幅度界的较宽来源：尖锐平方根边界

**定义 21.1（全制备的较宽实际域）。** 令

$$
\mathcal D_H=\{(t,p)\in\mathcal T\times(\mathbb R^3)^2:
q_0,q_1,q_2\le H\}.
$$

原树、叉积和 $\rho$ 都不变，制备允许任意大小及依赖叶对，没有 $L,d_0$ 条件。以相同三读距离及目标定义模量 $\Omega_H$。它是另一个实际来源问题，不替代定义16.1。

**定理 21.2（全制备的平方根上界）。** 对所有 $H>0,\varepsilon\ge0$，

$$
\Omega_H(\varepsilon)\le
\min\{2H^2,\max(2H\varepsilon,\sqrt6H^2\sqrt\varepsilon)\}.
$$

证明。推论16.3的 $|x_0\cdot w|\ge q_2^2$ 不需要叶界或非退化下界；定理5.1也覆盖依赖及零标签来源。任一实际对的 $|w-w'|\le2H\varepsilon$。零或同符号分支的目标差至多此量；异号分支满足

$$
q_2^2+(q'_2)^2\le|x_0\cdot w-x'_0\cdot w'|
\le H^2\varepsilon+H(2H\varepsilon)=3H^2\varepsilon.
$$

故目标差至多 $H(q_2+q'_2)\le\sqrt6H^2\sqrt\varepsilon$。最后每目标范数仍至多 $H^2$，给独立幅度截断。每个分支使用的两成员都在同一较宽实际域中。

**定理 21.3（保留原括号与联合限制的实际平方根尖锐对）。** 对每个 $H>0$ 有 $\Omega_H(\varepsilon)=\Theta(\sqrt\varepsilon)$ 当 $\varepsilon\downarrow0$。

证明。固定 $h_0,h_1\in(0,H)$。在正向正交标架中取足够小 $s>0$，置

$$
\begin{gathered}
r=\sqrt{h_1/s},\quad B=r^2,\quad \Delta=s^2,\quad
C=\sqrt{h_0^2h_1/s^3-s^2}>0,\\
b=re_1,\qquad a=(C/r)e_1+(s/r)e_2.
\end{gathered}
$$

直接计算得到

$$
A=h_0^2/s^2,\quad K=se_3,\quad V=rse_2,\quad
U=(s/r)(-se_1+Ce_2).
$$

取字面树 $t=\langle\alpha,\langle\alpha,\beta\rangle\rangle$，初值为 $U$、单位标签 $-f_2$。运输及五符号表给其一、二阶表达式 $-BK,-\Delta V$，故

$$
x_0=(s/r)(-se_1+Ce_2),\quad |x_0|=h_0,\quad
x_1=-h_1e_3,\quad x_2=-qe_2,\quad q=rs^3=\sqrt{h_1}s^{5/2}.
$$

令 $\theta=2\arctan(s/C)$，构造第二制备

$$
\begin{gathered}
b'=r(\cos\theta e_1+\sin\theta e_2),\quad K'=-se_3,\\
V'=rs(\sin\theta e_1-\cos\theta e_2),\qquad
a'=(C/B)b'+V'/B.
\end{gathered}
$$

$K'\times b'=V'$，并由 $b'\perp V'$ 得 $b'\times a'=K'$；后一个恒等式也可用 $b'\times(K'\times b')=BK'$ 核对。两制备的 $A,B,C,\Delta$ 完全相同。选第二字面树 $t'=\langle\langle\alpha,\beta\rangle,\alpha\rangle$，即在构造另一来源时反转根次序；它的初值为 $-U'$，标签 $+f_2$，两尾为 $BK',\Delta V'$。半角恒等式给

$$
\cos\theta=\frac{C^2-s^2}{C^2+s^2},\qquad
\sin\theta=\frac{2Cs}{C^2+s^2},\qquad
U'=\frac{CV'-\Delta b'}B=(s/r)(se_1-Ce_2)=-U.
$$

因此

$$
x'_0=x_0,\quad x'_1=x_1,\quad
x'_2=q(\sin\theta e_1-\cos\theta e_2).
$$

两来源的三范数同为 $(h_0,h_1,q)$，$s$ 足够小时同时在 $\mathcal D_H$。精确记录差与目标差分别为

$$
\begin{aligned}
\varepsilon_s&=2q\sin(\theta/2)
=\frac{2rs^4}{\sqrt{C^2+s^2}}=\frac{2s^5}{h_0},\\
|x_3-x'_3|&=2h_1q\cos(\theta/2)
=\sqrt2\,h_1^{3/2}\sqrt{h_0}\sqrt{\varepsilon_s}\cos(\theta/2).
\end{aligned}
$$

这里实际符号相反，$x_3=-(x_2\times x_1)$、$x'_3=x'_2\times x'_1$，所以不是环境符号分支假设。$s\downarrow0$ 时 $\cos(\theta/2)\to1$；$\varepsilon_s=2s^5/h_0$ 参数化每个足够小正误差，而非只给稀疏序列。由此得到全小误差的平方根下界，结合定理21.2完成尖锐阶。

该对的叶范数为 $|a|=h_0/s,|b|=\sqrt{h_1/s}$，都发散，且 $\Delta=s^2\to0$。因此它不属于任何固定 $L,d_0$ 的主域，不能反驳定理17.1，也不授予观察者根反转或制备旋转动作。

**推论 21.4（较宽域的条件有限读后果）。** 若定义20.1的同一准确制备／准确动作／联合读误差合同改用 $\mathcal D_H$，同一直接恢复器满足

$$
|\widehat x_3-x_3|\le b_\delta+2H\sqrt{p_\delta},\qquad
b_\delta=(2H+\delta)\delta,\quad
p_\delta=H^2\delta+(H+\delta)b_\delta.
$$

固定三读完整误差球下的最小最坏风险为 $\Theta(\sqrt\delta)$。

证明。若计算符号错误或为零而实际规则符号非零，则

$$
q_2^2\le|x_0\cdot w|
\le|x_0\cdot w-y_0\cdot\widetilde w|
\le\delta|w|+(H+\delta)b_\delta\le p_\delta.
$$

故 $|w|\le Hq_2\le H\sqrt{p_\delta}$，误差至多所列界；零或同符号分支有更小的 $b_\delta$ 界。对实际尖锐对在记录距 $2\delta$ 时使用共同中点回复，推论20.3的同一纤维论证给匹配下界。Dyadic 解码的读数／更新／位阶保持命题20.5所列，但有效输出容差需要平方量级的读误差预算。此处没有可用的统一 $c$，不能套用主域的线性系数。

## 22. 下一输出、准确全未来与全时间误差的区别

**命题 22.1（原实际域内的全未来不一致连续实例）。** 在 $L=2,H=4,d_0=1$ 的主域，若把目标距离改为扩展距离

$$
d_\infty=\sup_{j\ge3}|x_j-x'_j|\in[0,+\infty],
$$

则每个正的初始三读容差都允许 $d_\infty=+\infty$ 的实际对。

证明。取原叶树 $\alpha$，制备 $a=(3/2)e_1,b=(3/2)e_2$。叶范数小于2，$\Delta=81/16\ge1$，初始三范数 $3/2,3/2,9/4\le4$。规范结构递推使 $|x_j|=(3/2)^{F_{j+1}}$，方向循环在三条垂直轴上。绕 $e_3$ 以任意小非零正向角 $\theta$ 同时旋转两叶，保留树；所有初始限制准确保持，$x_0,x_1$ 差随角趋于零，$x_2$ 固定。未来反复出现的 $e_1,e_2$ 方向上的差为

$$
2\sin(\theta/2)(3/2)^{F_{j+1}}\longrightarrow+\infty.
$$

故任意正三读容差可容纳此对。轨道本身也不属于通常有界序列空间 $\ell^\infty$，所以这里使用扩展上确界距离而不虚称其中的有限范数。

本例只证明一组原参数下的全时间限制，不给全参数的时间一致分类。定理5.1的准确全未来相等、定理17.1的稳定下一输出、原制备恢复、同制备上下文与全时间误差是不同目标。零树的完整历史仍不给制备信息；定理6.3及11.1–11.3的上下文／制备纤维边界也保留。关系模型中的这些恢复结果不自动提供物理空间、时钟或记忆装置的识别。

## 23. 稳定性结果的来源、精确核验与保留边界

**约定 23.1（所复用接口及主要文献的准确范围）。** 来源与精确解释使用本卷第1–5节；组成支撑使用 [Process Geometry44.1–44.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)，一般恢复纤维使用 [Recovery Geometry3.1–3.4](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)。[Continuation13.2](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的实际像下降、共同来源及合法域饱和条件保留：准确因子化本身不保证稳定性、制备反演或未知制备间的上下文拼接。原单位方向的控制、Boundary43的另一初态／仪器及 Process44 的数量／方向读口，都不供应本卷的变化叶制备、读误差或额外动作。这里两成员的联合限制由每个实际树／制备见证承担，未用两个边缘的分别可行代替共同实现。

经典叉积基础为 `literature-attested`：Darpö，*Vector product algebras*，[arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，定义及 Lemma2。其特征不为2、交替双线性积、非退化对称型、循环配对与范数条件在定向正定实三维中成立；这里只复用其垂直性及重复向量恒等式，不重复主张向量积分类。

McShane，*Extension of range of functions*，*Bulletin AMS* 40，837–842，[原文](https://www.ams.org/journals/bull/1934-40-12/S0002-9904-1934-05978-0/S0002-9904-1934-05978-0.pdf)，Theorem1 的前提是任意度量空间子集上的实值 Lipschitz 函数，不要求子集闭合或紧致。命题20.4严格使用这一范围，并直接给出上确界的有限性、像内一致与 Lipschitz 证明；它不把数学延拓称为有限取得算法。

Foucart、Liao，*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, but what of the Parameter?*，[arXiv:2111.02601v1](https://arxiv.org/pdf/2111.02601v1)，Introduction1.1–1.2 的模型／数据一致纤维及确定最坏误差提供背景。将本卷实际四向量图嵌入 $\mathbb R^{12}$，观察及目标可写成线性坐标投影，但实际模型集仍是原树／制备的图，不能改成环境线性空间。该文专门正则化结果需要 Hilbert 近似模型 $\operatorname{dist}(f,V)\le\epsilon$、Euclidean 数据噪声、$V\cap\ker\Lambda=\{0\}$，部分还需正交归一表示子；本卷实际图及分块最大误差合同没有建立这些前提，不调用其专门算法或最优参数结论。一般候选纤维／选择、协变性、Fibonacci 闭式、范数不等式与分段线性优化都是复用基础。

实际投影幅度约束、无界树及变化制备的模量、准确阈值与有限算术取得后果，以及另域的实际平方根尖锐对，是声明源合同下的仓内综合推导（`repo-derived`）。这里只提供普通数学证明和有限精确佐证，不新增 Lean 核验、不作全球原创性或文献穷尽声明。

**约定 23.2（针对有限算术与阈值的精确核验结果）。** 有理数核验取1–4叶全部102棵字面有序树，及三个制备

$$
\begin{aligned}
p_1&=((1,0,0),(0,1,0)),\\
p_2&=((3/2,1/2,0),(1/2,3/2,1/2)),\\
p_3&=((1/2,1,1/2),(1,-1/2,1)).
\end{aligned}
$$

在 $L=3,H=16,d_0=1$ 下有274个允许树／制备对。对 $b=0,1,2,3,4$ 将各坐标舍入至最近 $2^{-b}$ 格点，再分别使用未附加扰动、或在九个坐标之一附加 $\pm2^{-b},\pm2\cdot2^{-b}$ 共37种回复；同时误差界取 $\delta=3\cdot2^{-b}$。有理平方范数准确核对了50,690个回复实例的误差合同和定理20.2，包含41,070个真实零叉积、9,347个相同符号、188个计算零符号与85个相反符号实例。实际四向量以原括号求值及定理3.1运输取得；没有把带噪回复当作精确实际记录。

两项另外的有理端点核对取 $\eta=7/5,17/11$，较小端点列表的 $m$ 上限分别为5、16，含8、63个混合组成；准确 $\mathbb Q(\sqrt5)$ 加权截止列表含81、768个支持组成。三线交点优化与端点公式分别给共同指数 $3/5,4/11$，实际组成见证为 $(1,2),(3,5)$。这些有限核验可检出有限算术或有限列表的错误；所有列表覆盖、临界未达到、任意制备、任意树大小及全小误差尖锐阶仍由第16–22节的普通证明承担，不以样本给无限结论或给原来源加大小配额。

**约定 23.3（已回答的任务与尚需单独合同的问题）。** 开放问题15.2的下一向量稳定性及准确零／线性制度由定理17.1–19.3给出；有限误差取得由定义20.1的额外仪器承诺支持，较宽来源与全未来分别按第21、22节的量词承担。最优常数、更丰富付费协议的下界、制备／动作不确定性、物理认证与价格、另供随机规律、任意上下文及全参数全时间分类均需另外研究，未作为这里的前提。抽象上确界、选择或参数存在与有限算法分开；原源、操作、记录、精度及共同实现的限制不因某个恢复公式而消失。

## 追加锚（本行以下为增补区）
## 24. 固定三向量记录的全时间模量

本节至第32节保持定义16.1的全部实际来源及定义20.1的一条取得历史，将目标从下一向量改为所有 $j\ge3$ 的共同误差上确界。原树大小和预测时刻都无统一上限，原制备在每个来源的执行中固定。第1–5节的精确恢复、第16–19节的实际投影与存在性阈值直接复用；下一向量连续不自动给出本节的全时间结论。

**定义 24.1（全时间扩展距离与模量）。** 固定 $L,H>0$、$0<d_0<L^4$，取 $\mathcal D=\mathcal D_{L,H,d_0}$。对 $s=(t,p),s'=(t',p')\in\mathcal D$ 置

$$
\begin{aligned}
d_3(s,s')&=\max_{0\le i\le2}|x_i(s)-x_i(s')|,\\
d_\infty(s,s')&=\sup_{j\ge3}|x_j(s)-x_j(s')|\in[0,+\infty],\\
\Omega(\varepsilon)&=\sup_{\substack{s,s'\in\mathcal D\\d_3(s,s')\le\varepsilon}}d_\infty(s,s')\qquad(\varepsilon\ge0).
\end{aligned}
$$

空上确界取零。每对的两个成员分别满足两叶界、$\Delta\ge d_0$ 和三个读数界；不以环境三元组代替实际像。记

$$
\begin{gathered}
\varphi=(1+\sqrt5)/2,\quad \psi=-1/\varphi,\quad
s_0=\sqrt{d_0},\quad z=\log s_0,\quad\ell=\log L,\\
G=\varphi^2z-\ell=\varphi^2\gamma,\qquad
D_{\rm crit}=L^{2/\varphi^2},\qquad c=s_0/L^2\in(0,1),\\
F_0=0,\quad F_1=1,\quad F_{n+2}=F_{n+1}+F_n.
\end{gathered}
$$

这里 $\gamma$ 恰为定义18.1的参数，$H_*$ 恰为定理18.4的实际达到阈值，不另定义不同的阈值。$U,V$ 继续使用定义16.1的记法。

**定理 24.2（原全来源的完整全时间制度）。** 对每组站立参数，$\Omega(0)=0$。正误差下的制度如下；$\Theta$ 均指 $\varepsilon\downarrow0$、系数可依固定 $L,H,d_0$。

| 24实际参数制度 | 全时间结论 |
| --- | --- |
| 24收缩叶界 $L<1$，任意 $H>0$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24单位叶界 $L=1,H<1$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24单位叶界 $L=1,H\ge1$ | $\Omega(\varepsilon)=1$，$0<\varepsilon\le(2+6/c)^{-1}$ |
| 24可达收缩 $L>1,d_0<D_{\rm crit},H<1$ | $\Omega(\varepsilon)=\Theta(\varepsilon)$ |
| 24可达临界近似 $L>1,d_0<D_{\rm crit},H=1$ | $\Omega(\varepsilon)=1$，$0<\varepsilon\le(2+6/c)^{-1}$ |
| 24超单位读界 $L>1,d_0<D_{\rm crit},H>1$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$ |
| 24临界排除 $L>1,d_0=D_{\rm crit},H\le1$ | $\Omega\equiv0$ |
| 24临界超单位读界 $L>1,d_0=D_{\rm crit},H>1$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$ |
| 24正增长但未达阈值 $L>1,d_0>D_{\rm crit},H<H_*$ | $\Omega\equiv0$ |
| 24正增长且达到阈值 $L>1,d_0>D_{\rm crit},H\ge H_*$ | 每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)=+\infty$，包括 $H=H_*$ |

在线性行，令 $M=\min(L,H)<1$，则每个误差下 $\Omega\le2M^2$，且有定理26.2的全时间线性上界。在两个单位平台行，所有误差下 $\Omega\le2$，并且 $\varepsilon\ge2$ 时恰等于2。除此之外的有限误差完整曲线及最优线性系数未在此确定。

证明。定理5.1在实际三读像上恢复完整未来，故 $d_3=0$ 迫使全部未来相同。零 cherry 在任意允许正交制备处供应全零历史，$\mathcal D$ 非空。引理25.1–25.2给增长制度，定理26.2–26.3给全部线性行，定理27.1–27.4给两平台行及两个误差端点，定理28.1–28.2给零与无穷行。若 $L\le1$，站立条件 $z<2\ell$ 强迫 $G<0$；若 $L>1$，$G$ 的符号恰为 $d_0-D_{\rm crit}$ 的符号。因此各行互斥且穷尽全部参数。

## 25. 正幅度增长与既有实际阈值的对应

**引理 25.1（实际尾的增长判据）。** 非零尾的 $r=|b|,s=\sqrt\Delta$、$\nu(t)=(m,n)$ 沿用定理4.3。置

$$
\Gamma(p)=\log r+\varphi\log s.
$$

则 $\Gamma<0,=0,>0$ 分别使 $q_j\to0,1,+\infty$。方向保留定理4.3的三循环；零标签来源的全部 $j\ge1$ 向量仍为零。

证明。定理4.3给 $q_{j+2}=q_jq_{j+1}$，两个初值严格为正。归纳得到经典正输入乘法递推的公式

$$
q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\qquad(j\ge2).
$$

取对数，特征根为 $\varphi,\psi$，主项系数的符号是 $\log q_1+\varphi\log q_2$ 的符号。实际齐次性给

$$
\log q_1+\varphi\log q_2=(m+\varphi n)\Gamma(p).
$$

非空树使 $m+\varphi n>0$。主项为零时只剩 $O(\varphi^{-j})$，所以幅度趋于1；其余主项趋于正或负无穷，得到另两结论。先分出实际零尾再取对数，不删除零分支。

**引理 25.2（原叶界允许的增长参数）。** 两叶界及行列式下界所容许的 $(r,s)$ 恰为

$$
s\ge s_0,\qquad s\le Lr,\qquad r\le L.
$$

因此 $\min\Gamma=G$，在 $(a,b)=(Le_1,(s_0/L)e_2)$ 达到；$\max\Gamma=(1+2\varphi)\ell$，在两正交叶长均为 $L$ 时达到。

证明。$s^2=\Delta\le|a|^2|b|^2$ 给必要性。每个所列 $(r,s)$ 都由同一正交制备 $((s/r)e_1,re_2)$ 实现。给定 $s$，最小 $r$ 是 $s/L$，于是 $\Gamma\ge\varphi^2\log s-\ell\ge G$；两者等号同时由所列端点达到。另一方面 $r\le L,s\le L^2$，得最大值及其正交达到。

**约定 25.3（同一个有限阈值及两处未达到端点）。** 定理18.2的 $f_0,f_1,f_2$、区间 $I=[z-\ell,\ell]$ 和实际组成支撑 $\mathcal S$ 原样复用。其三线不等式有实际树／正交制备的反向见证；组成列表只为证明或离线存在性计算服务，没有给观察者组成口或来源大小上限。

在 $G>0$ 时，可把同一个 $H_*$ 写为较小截止

$$
\begin{gathered}
Q=\frac{\varphi^2z}{G},\qquad
\mathcal F_0=\{(m,n)\in\mathcal S:m+\varphi n\le Q\},\\
\log H_*=
\min_{(m,n)\in\mathcal F_0}\min_{v\in I}\max(f_0(v),f_1(v),f_2(v)).
\end{gathered}
$$

对应证明就是命题19.1的较小截止：若三读上界不超过 $s_0$，则

$$
(m+\varphi n)G\le\log q_1+\varphi\log q_2\le\varphi^2z.
$$

原叶 $\alpha$ 在等叶长 $\sqrt{s_0}<L$ 处已有上界 $s_0$；故每个可能持平或改善者都在 $\mathcal F_0$。定理18.4所用较宽列表的截止为 $\varphi z/\gamma=\varphi Q$；两列表保留相同完整三线检验，覆盖所有优化者，因此最小值及实际达到身份相同。以 $m+n\le\lfloor Q\rfloor$ 或更宽总数截止代替加权列表也可以，条件是仍只用 $\mathcal S$ 并检验全部三线；覆盖不意味着每个所留组成都可行。若采用 $G/\varphi$ 而非 $\gamma=G/\varphi^2$ 作为增长记法，也必须把截止乘数同时换算，不能仅比较参数名称。

所以 $G<0$ 的非零三读上界下确界为0而不达到，$G=0$ 的下确界为1而不达到，$G>0$ 的 $1<H_*\le s_0$ 有实际达到者；这是定理18.3–18.4的同一端点结论。定理19.2–19.3的端点变量 $\eta=\ell/z-1$ 及有限公式也不变：$d_0\ge L$ 时 $H_*=s_0$，$D_{\rm crit}<d_0<L$ 时 $1<H_*<s_0$；$\eta=\varphi$ 是未达到的临界1，$\eta>\varphi$ 是未达到的0。这些既有阈值与例19.4覆盖的 $L=e,d_0=e^{4/5},H_*=e^{1/5}$ 都不是另一个全时间结果。

## 26. 非负单项式的全时间界与尖锐线性阶

**引理 26.1（三个对应锚与第一锚误差）。** 假设两实际来源的 $q_0,q_1,q_2$ 均不超过 $M>0$，且 $d_3\le\varepsilon$。置

$$
K(M)=2M+\frac{2M(2M+1)}c.
$$

则 $|x_3-x'_3|\le K(M)\varepsilon$。对单个来源及 $j\ge3$，记

$$
a_j=F_{j-2},\quad b_j=F_{j-1},\quad
k_j=1+((j-1)\bmod3).
$$

有不含负指数或除法的实际公式

$$
x_j=
\begin{cases}
q_1^{a_j-1}q_2^{b_j}x_1,&k_j=1,\\
q_1^{a_j}q_2^{b_j-1}x_2,&k_j=2,\\
q_1^{a_j-1}q_2^{b_j-1}x_3,&k_j=3.
\end{cases}
$$

约定 $0^0=1$，零尾也满足公式；$j=3$ 的最后一个系数恰为1。

证明。非零尾用定理4.3的三循环和引理25.1的正幅度式，同一相位的向量与相应锚同向，直接得到三个系数。此范围 $a_j,b_j\ge1$，故指数非负；零尾的三个锚均零，不作除法仍得准确值。

为给第一锚的充分系数，写 $w=x_2\times x_1$，双线性给 $|w-w'|\le2M\varepsilon$。同号或任一零尾由定理5.1直接使用此界。若两非零实际符号相反，三个归一化读数的有符号三重积各自绝对值至少为 $c$，差至少 $2c$。不等式

$$
\left|\frac{x}{|x|}-\frac{y}{|y|}\right|\le\frac{2|x-y|}{|x|}
$$

及三重积逐因子相减给

$$
2c\le2\varepsilon(q_0^{-1}+q_1^{-1}+q_2^{-1})
\le\frac{2\varepsilon(2M+1)}{q_2}.
$$

末步用推论16.3的 $q_2\le q_0q_1$ 及 $q_0,q_1\le M$，得 $q_0,q_1\ge q_2/M$。所以 $q_2\le(2M+1)\varepsilon/c$；实际异号目标差至多

$$
|w-w'|+2|w|\le2M\varepsilon+2Mq_2\le K(M)\varepsilon.
$$

归一化只用于证明且各所除量已非零。这个第一锚系数是既有下一步线性控制的一个充分推论，不主张新的下一步最优常数。

**定理 26.2（原全树的全时间线性上界）。** 在定理24.2的线性行，令 $M=\min(L,H)<1$、$K_0=\max(1,K(M))$，则对每个 $\varepsilon\ge0$，

$$
\Omega(\varepsilon)\le
\min\left\{2M^2,\left(K_0+\frac{M}{(1-M)^2}\right)\varepsilon\right\}.
$$

证明。若 $L\le1$，由 $|u\times v|\le|u||v|$ 的结构归纳，任意非空原树 $u$ 满足 $|E_p(u)|\le L^{\#\text{叶}(u)}\le L$；每个替换树仍是这样的树。三读界又给 $q_0,q_1,q_2\le H$，故三锚的前两个范数至多 $M$，第三为 $q_1q_2\le M^2\le M$。若 $L>1,H<1$，直接由三读界得到相同结论。

对 $[0,M]^2$ 上总次数为 $n$ 的非负单项式，逐个相减其 $n$ 个因子给大小至多 $M^n$、两值之差至多 $nM^{n-1}\varepsilon$；次数0的差为零。$q_1,q_2$ 的范数差均至多 $\varepsilon$。引理26.1的每个未来向量是一个这样的系数乘相应锚，锚差至多 $K_0\varepsilon$、锚范数至多 $M$，所以向量差至多

$$
(K_0M^n+nM^n)\varepsilon
\le\left(K_0+\sum_{n\ge1}nM^n\right)\varepsilon
=\left(K_0+\frac M{(1-M)^2}\right)\varepsilon.
$$

这个界同时覆盖所有 $j$、所有树和全部零／符号分支，未固定预测时刻或来源大小。正幅度递推还给每个 $j\ge3$ 的范数至多 $M^2$，于是另有 $2M^2$ 界。

**定理 26.3（线性行的实际尖锐对）。** 每个线性行都有正数 $b,\varepsilon_0$ 使 $\Omega(\varepsilon)\ge b\varepsilon$，$0<\varepsilon\le\varepsilon_0$。

证明。引理25.2及站立条件给这些行的 $G<0$；定理18.3供应一个有限实际树及允许制备，其 $x_3\ne0$。固定该来源，令 $M_0=\max(q_0,q_1,q_2)>0$。复用定理17.2的正向旋转对：旋转轴垂直于 $x_3$，并取 $2\sin(\theta/2)=\varepsilon/M_0$，$0<\varepsilon\le2M_0$。同时旋转所供的两个叶并保留同一字面树，叉积等变使全部输出同旋转；两来源的 Gram、叶界与三读范数界逐项保持。记录差至多 $\varepsilon$，$j=3$ 差恰为 $(q_3/M_0)\varepsilon$。故全时间上确界至少为此值。此处构造静态竞争来源，没有给观察者旋转动作。

## 27. 精确单位平台与两套实际收缩族

**定理 27.1（对应锚给局部精确平台上界）。** 在两个单位平台行，$\Omega\le2$，且 $0<\varepsilon\le(2+6/c)^{-1}$ 时 $\Omega(\varepsilon)\le1$。

证明。$L=1$ 或 $H=1$ 都给 $q_0,q_1,q_2\le1$，全部未来范数至多 $q_1q_2\le1$。引理26.1把每个未来写为同相位锚的 $[0,1]$ 系数倍；三个对应锚的距离分别至多 $\varepsilon,\varepsilon,K(1)\varepsilon$，范数至多1。对任意 $u,v$ 及 $\alpha,\beta\in[0,1]$，凸性给

$$
|\alpha u-\beta v|\le\max\{0,|u|,|v|,|u-v|\}.
$$

具体把 $\alpha u-\beta v$ 写成四角值 $0,u,-v,u-v$ 的双线性权重之和即可。$K(1)=2+6/c$，所以规定范围内每个同相位差都至多1。零及异号锚也受同一凸性界控制。

**定理 27.2（原规范树的实际单位平台下界）。** 两个平台行的每个 $\varepsilon>0$ 都有 $\Omega(\varepsilon)\ge1$。在 $L>1,d_0<D_{\rm crit},H=1$ 行，下界可完全由每个成员都严格收缩的实际来源对给出，包含 $1<d_0<D_{\rm crit}$。

证明。若 $L=1,H\ge1$，用同一树 $\alpha$，分别供应 $(e_1,e_2)$ 与 $(\lambda e_1,\lambda e_2)$，$\lambda<1$ 趋于1且 $\lambda^4\ge d_0$。两者全部联合限制成立，记录距离 $1-\lambda^2\to0$。前者每个幅度为1，后者的规范幅度为 $\lambda^{F_{j+1}}\to0$，方向相同，故全时间差上确界为1。

以下取第二个平台行。选择

$$
\max(1,s_0)<s_*<L^{1/\varphi^2},\quad
A_*=s_*^{\varphi^2},\quad r_*=s_*^{-\varphi},\quad
p_*=(A_*e_1,r_*e_2),\quad C_*=\log A_*>0.
$$

$A_*,r_*<L$，$\Delta_*=s_*^2>d_0$，且 $\Gamma(p_*)=0$。原规范树 $T_l=\rho^l\alpha$ 的方向循环为 $e_1,e_2,e_2\times e_1$，幅度的准确对数为 $C_*\psi^l$。其原始组成与叶数是

$$
\nu(T_l)=(F_{l-1},F_l)\ (l\ge1),\qquad
N_l=\#\text{叶}(T_l)=F_{l+1}\ (l\ge0).
$$

两个初始树都恰一叶，结构递推给 $N_{l+2}=N_{l+1}+N_l$；组成则按原 $M$ 递推，证明上述索引。因而同乘原叶以 $e^{-\tau}$ 的准确缩放因子是 $e^{-\tau F_{l+1}}$。

令 $k\to\infty$ 只取正的12倍数，定义

$$
\tau_s=\frac{2(1+C_*)\varphi^{-k}}{F_{k+1}},\qquad
\tau_f=\varphi^{k/2}\tau_s.
$$

比较同一实际树 $T_k$ 在两个固定制备 $e^{-\tau_s}p_*$ 和 $e^{-\tau_f}p_*$ 下的历史。两种叶缩放均不增加叶范数；$\tau_f\to0$ 使两行列式 $\Delta_*e^{-4\tau}$ 最终都至少 $d_0$。对取得偏移 $h=0,1,2$，其六个准确对数为

$$
C_*\psi^{k+h}-\tau F_{k+h+1},\qquad \tau\in\{\tau_s,\tau_f\}.
$$

正项至多 $C_*\varphi^{-k}$；即使较小的减项也至少 $2(1+C_*)\varphi^{-k}$。所以六个读数范数都不超过1。固定 $h$ 时这些对数趋于0，且 $k\equiv0\pmod3$ 固定共同三轴相位，因此 $d_3\to0$。

取相对预测时刻 $j_k=3k/4\equiv0\pmod3$。Binet 公式给 $F_{k+j_k+1}/F_{k+1}\asymp\varphi^{j_k}$，从而

$$
\tau_sF_{k+j_k+1}\to0,\qquad
\tau_fF_{k+j_k+1}\to+\infty,\qquad
C_*\psi^{k+j_k}\to0.
$$

两幅度在同一轴上分别趋于1和0。给定任意固定正 $\varepsilon$，最终记录距离不超过它，未来距离可任意接近1，故 $\Omega(\varepsilon)\ge1$。每个成员却有 $\Gamma=-(1+2\varphi)\tau<0$，确实逐个收缩。若 $d_0>1$，任意允许非零历史都必须收缩：三读界给 $\log q_1,\log q_2\le0$，故 $\Gamma\le0$；等号会迫使 $q_1=q_2=1$。组成矩阵的行列式 $m^2+mn-n^2\ne0$（定理6.4的整数／无理根论证）继而迫使 $r=s=1$，与 $\Delta\ge d_0>1$ 矛盾。因此此子制度没有中性来源，下界仍成立。

**命题 27.3（正奇／奇实际树的同一平台见证）。** 第二个平台行也有完全由正奇／奇组成实际树给出的严格收缩对。

证明。选 $\max(1,d_0)<D<D_{\rm crit}$，供应临界制备

$$
p_*=(D^{\varphi^2/2}e_1,D^{-\varphi/2}e_2).
$$

它有严格叶界、$\Delta=D>d_0$。取 $m_h=F_{3h+1},n_h=F_{3h+2}$，$h\ge0$。Fibonacci 递推模2的周期3表明二者都是奇数。使用 Process44.2 从 $\langle\beta,\alpha\rangle$ 双左接标签的实际配方，取得组成 $(m_h,n_h)$ 的非零树；必要时在构造另一来源时反转其根，使单位标签恒为 $+f_3$。每个成员使用这一确定符号的实际树及同一所供制备，不能把组成与方向的两个边缘分别实现。

置 $\delta_h=n_h-\varphi m_h=\psi^{3h+1}$，临界制备的三个初始对数为

$$
w_0=-\tfrac12\varphi\log D\,\delta_h,\qquad
w_1=\tfrac12\log D\,\delta_h,\qquad w_2=w_0+w_1.
$$

令 $e_h=\max(|w_0|,|w_1|)>0$、$\beta_h=2e_h/(m_h+n_h)$，实际供应 $e^{-\beta_h}p_*$。同叶缩放分别从前两对数减去 $(m_h+n_h)\beta_h$、$(m_h+2n_h)\beta_h$，第三对数为前两项之和。因此三个对数都负，且趋于0；$\beta_h\to0$ 保留最终两叶界及行列式下界，$\Gamma<0$。所有记录趋于同一个单位三轴记录 $(f_3,f_1,f_2)$。

给定 $\varepsilon>0$、$\xi\in(0,1/2)$，先选一个最终允许的 $h$，使其记录距该单位记录小于 $\varepsilon/2$。它严格收缩，故有某个 $J\ge3$ 使 $q_J<\xi$。固定这个 $J$ 后，再选更大的 $h'$：其记录仍距单位记录小于 $\varepsilon/2$，而引理26.1在这个固定有限时刻的单项式式使 $q'_J>1-\xi$。两个实际来源相位、符号一致，记录距小于 $\varepsilon$，未来距大于 $1-2\xi$。令 $\xi\downarrow0$ 得同一下界。这一构造与定理27.2共同证明无一致收缩裕量的原来源障碍，不是以标量环境模型代替实际树。

**定理 27.4（单位平台的大误差端点）。** 两个平台行在 $\varepsilon\ge2$ 时均有 $\Omega(\varepsilon)=2$。

证明。上界见定理27.1。若 $L=1$，取单位制备处的 $\langle\beta,\alpha\rangle$ 与根反序树；两个三读及所有未来均为相反单位向量，$d_3=2,d_\infty=2$。若 $L>1,H=1$，取定理27.2中足够晚的任一收缩 $T_k$，及在同一制备处反转它根的实际树。$k\ge2$ 时它确是内部树，原 $\rho$ 保持根的反转且叉积取负，故每个时刻两输出相反。两者全部限制成立，$d_3\le2$；固定相对时刻3的 $q_3\to1$，其距离 $2q_3\to2$。因此上确界2成立，不要求允许的中性树或最大值达到。

## 28. 全零未来与每个正误差的实际无穷对

**定理 28.1（准确零制度）。** 若 $G=0,H\le1$，或 $G>0,H<H_*$，则所有实际未来 $x_j,j\ge3$ 均零，$\Omega\equiv0$。

证明。定理18.3–18.4排除全部非零标签尾；定理4.3给剩余来源的全零尾。这不宣称原初值零或来源域为空。例19.4在每组站立参数都给实际零标签、非零初值见证：取 $a=Le_1,b=\xi e_1+(s_0/L)e_2$，$\xi>0$ 足够小，使 $|b|\le L$ 且 $L\xi s_0\le H$。字面树 $\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle$ 的初值为 $CK\ne0$、范数 $L\xi s_0$，$\Delta=d_0$，三个取得值及全零尾同时合法。

**定理 28.2（准确无穷制度及阈值等号）。** 若 $L>1,G\le0,H>1$，或 $L>1,G>0,H\ge H_*$，则对每个 $\varepsilon>0$ 都有一对同时允许的实际来源满足 $d_3\le\varepsilon$、$d_\infty=+\infty$。

证明。先构造一个允许的非零增长来源。在 $G<0$ 时选择 $\max(1,s_0)<s<L^{1/\varphi^2}$，在 $G=0$ 时取 $s=s_0=L^{1/\varphi^2}$。临界正交制备 $a=s^{\varphi^2}e_1,b=s^{-\varphi}e_2$ 的规范幅度趋于1，所以某个固定有限 $T_k$ 的三个读数都严格小于 $H$。保留 $s$，把 $r=s^{-\varphi}$ 改成 $re^v$，同时把第一叶长改成 $s/(re^v)$。取足够小 $v>0$，第一叶不增加、第二叶仍不超过 $L$，$\Delta=s^2\ge d_0$ 不变。这个固定有限树的三个多项式求值连续，故三个严格读界也保持，而 $\Gamma$ 变为 $v>0$。这里有限连续性只构造一个共同实现的增长来源，未据此断言全时间连续。

在 $G>0,H\ge H_*$ 时，直接使用定理18.4的实际达到者；引理25.2给其 $\Gamma\ge G>0$，包括准确等号 $H=H_*$。

固定上述任一实际增长来源。绕其 $x_1$ 轴作任意小非零正向旋转 $Q_\theta$，第二来源保留原树、供应 $(Q_\theta a,Q_\theta b)$。所有 Gram、叶界及三个读数范数完全保持；角度足够小使 $d_3\le\varepsilon$。$x_2$ 相位垂直于旋转轴；在 $j\equiv2\pmod3$ 的无穷时刻，实际差为 $2\sin(\theta/2)q_j\to+\infty$。这是一个实际成对来源的无限距离，不是分别可达的两个边缘极值；旋转不成为观察者端口。

## 29. 只用含误差旧记录的全时间数值求值器

**定义 29.1（裁剪、第三锚及非负幂求值）。** 在线性行使用公共域界 $M=\min(L,H)<1$。对任意有限实向量报告 $y_0,y_1,y_2$，令 $P_M$ 为到闭 Euclidean $M$ 球的径向投影，计算

$$
Y_i=P_M(y_i),\quad W=Y_2\times Y_1,\quad
Z=P_M\!\left(\operatorname{sgn}(Y_0\cdot W)W\right),\quad
\widehat u=|Y_1|,\quad\widehat v=|Y_2|.
$$

$\operatorname{sgn}(0)=0$。对每个请求的 $j\ge3$，用引理26.1的 $a_j,b_j,k_j$ 返回

$$
\widehat x_j=
\begin{cases}
\widehat u^{a_j-1}\widehat v^{b_j}Y_1,&k_j=1,\\
\widehat u^{a_j}\widehat v^{b_j-1}Y_2,&k_j=2,\\
\widehat u^{a_j-1}\widehat v^{b_j-1}Z,&k_j=3.
\end{cases}
$$

次数0的幂为1。公式对零、非正交、错号及不在实际记录像上的报告都定义；它是保留报告的数值后处理，裁剪不执行源的归一化，也不生成新的制备、读数或动作。

**定理 29.2（全部报告分支的统一第一锚控制）。** 若实际来源在该线性行且同时满足 $|y_i-x_i|\le\delta$、$i=0,1,2$、$\delta\ge0$，则

$$
|Z-x_3|\le K_{\rm err}\delta,\qquad
K_{\rm err}=2M+\frac{4M(2M+1)}c.
$$

证明。径向公式给对球内每个 $z$，$(v-P_Mv)\cdot(z-P_Mv)\le0$。代入 $z=P_Mw$，再加交换 $v,w$ 后的不等式，得

$$
|P_Mv-P_Mw|^2\le(v-w)\cdot(P_Mv-P_Mw)
\le|v-w|\,|P_Mv-P_Mw|.
$$

所以 $P_M$ 为1-Lipschitz，球内点不动，$|Y_i-x_i|\le\delta$。真实 $x_3$ 在球内，最后投影不增加它的误差。设 $w=x_2\times x_1$，双线性给 $|W-w|\le2M\delta$。

真实零尾时 $x_1=x_2=0$，于是 $|W|\le M\delta$，不论报告初值或计算符号为何。真实非零尾而计算符号正确时，投影前误差至多 $2M\delta$。若 $Y_0=0$，$q_0\le\delta$，推论16.3给 $q_2\le M\delta$，计算输出为零且 $|x_3|\le M^2\delta$。若 $Y_1=0$ 或 $Y_2=0$，相应真实范数至多 $\delta$，$W=0$ 且 $|x_3|\le M\delta$。这些情况都满足所述系数。

余下真实三个向量及三个 $Y_i$ 均非零。它们的归一化三重积之差至多

$$
2\delta(q_0^{-1}+q_1^{-1}+q_2^{-1})
\le\frac{2\delta(2M+1)}{q_2}.
$$

若计算符号错误或为零，真实归一化三重积的绝对值至少 $c$，报告的该值异号或零，所以 $q_2\le2(2M+1)\delta/c$。此时投影前误差至多

$$
|W-w|+2|w|\le2M\delta+2Mq_2\le K_{\rm err}\delta.
$$

$W=0$ 而各 $Y_i\ne0$ 的平行报告也在此三重积为零的分支中；证明未假设报告正交或可实现。所用归一化只为估计，定义29.1的求值器不除任何取得幅度。$\delta=0$ 时定理5.1及实际单项式式直接给准确结果。

**定理 29.3（显式记录求值器的全时间精度）。** 在定理29.2的全部条件下，

$$
\sup_{j\ge3}|\widehat x_j-x_j|
\le\left(\max(1,K_{\rm err})+\frac M{(1-M)^2}\right)\delta.
$$

证明。$\widehat u,\widehat v,q_1,q_2\in[0,M]$ 且相应范数差至多 $\delta$；三个真实和计算锚的范数都至多 $M$，锚误差分别至多 $\delta,\delta,K_{\rm err}\delta$。按定理26.2的逐因子单项式估计，对每个对应相位给同一个总次数界，再用 $\sum_{n\ge1}nM^n=M/(1-M)^2$。全证明只把报告当作数值输入，从未当成新的实际来源。故结论同时覆盖全部树大小、全部预测时刻和所有像外分支。

定理20.2的既有直接符号／叉积恢复器也可作为第三锚：在 $\delta\le1$ 时，以其已证充分系数代入同一个全时间单项式估计，得到另一有效线性上界。定义29.1的公共界裁剪与上述系数只是全时间实现的一种选择，不主张第一步位成本或最优常数优于命题20.5。

**推论 29.4（所声明理想运算的成本）。** 对单个请求时刻 $j$，定义29.1可用 $O(j)$ 次理想单位成本整数／实标量运算、$O(j)$ 位宽的指数和固定维数实数工作寄存器求值。

证明。逐次整数递推用 $O(j)$ 次加法取得 Fibonacci 指数，Binet 式给其位宽 $\Theta(j)$；固定数量的幂各用反复平方，乘法数 $O(\log F_j)=O(j)$。裁剪、范数、叉积、点积、准确符号及向量缩放各只有固定次数。九个原报告坐标可原样保留，三个派生锚及两个范数可在固定维数 scratch 中每次重算，或以另计缓存存储保留。请求索引／计数器和每个输出仍分别收费。

这里整数增长字的运算不是单位位工作，实数范数、径向投影的除法、准确符号及公共常数均需另给表示合同。推论仅为理想运算计数，不提供任意实数的有效符号 oracle、全时间舍入精度日程或物理执行成本；无限输出序列也不在有限时间内整体发射。

## 30. 固定取得记录的风险与同时资源

**定义 30.1（确定同时误差的完整序列风险）。** 保持定义20.1的准确制备／准确原动作，三次 Read、两次 $\rho$ 后 Stop；只有旧报告和同一日程／来源版本／时间／动作／Stop 身份可用，不供应来源大小或计时侧信道。允许所有确定集合函数 $R:(\mathbb R^3)^3\to(\mathbb R^3)^{\{j\ge3\}}$，置

$$
\mathcal R_\delta=
\inf_R\sup_{\substack{s\in\mathcal D\\ |y_i-x_i(s)|\le\delta\ (0\le i\le2)}}
\sup_{j\ge3}|R(y)_j-x_j(s)|.
$$

未加效率、可测性或连续性条件。报告误差可完全相关、联合对抗且依赖历史。

**推论 30.2（实际全时间风险制度）。** 对每个 $\delta\ge0$，

$$
\tfrac12\Omega(2\delta)\le\mathcal R_\delta\le\Omega(2\delta).
$$

准确数据有 $\mathcal R_0=0$。线性行的风险为 $\Theta(\delta)$，定理29.3给显式仅用记录的理想运算上界；零行的类感知常零预测准确。平台行每个 $\delta>0$ 都有 $1/2\le\mathcal R_\delta\le1$，且 $\delta\ge1$ 时恰为1。无穷行每个 $\delta>0$ 都有 $\mathcal R_\delta=+\infty$。

证明与复用对应。沿用推论20.3的候选纤维比较，将目标从 $x_3$ 换成完整 $j\ge3$ 序列及扩展上确界距离；该距离的三角不等式逐时刻成立，取上确界仍成立。任意 $d_3\le2\delta$ 的实际对共享逐分量中点报告，任一共同预测在某一端的全时间误差至少为两序列距离的一半，得到下界，包括无穷。每个非空兼容纤维选一个实际来源并报告其准确未来，其它兼容记录与它距离至多 $2\delta$，得到抽象上界；空纤维任取输出。此选择不供应有限成员检验或来源搜索。线性阶由定理26.3及29.3，平台下界由任意正容差的单位平台，平台上界由常零预测，无穷由定理28.2。$\delta\ge1$ 时定理27.4的 $\Omega(2\delta)=2$ 给平台风险的等号。

**推论 30.3（同一实现的取得、位表示与源代码费用）。** 本任务的原取得为

$$
\operatorname{Read}(x_0),\rho,\operatorname{Read}(x_1),\rho,
\operatorname{Read}(x_2),\operatorname{Stop}.
$$

恰有3次完整向量 Read、2次原破坏性更新、每回复宽3及九个保留数值坐标，停止时源是 $\rho^2t$。这些调用与定义29.1的预测算术分开；域／精度承诺 $L,H,d_0,\delta$ 由供应者承担，记录元数据不夹带语法、组成或校准。

若另外声明一个有界坐标格点表示，逐坐标步长至多 $2\xi/\sqrt3$ 可使单向量量化误差至多 $\xi$。在原报告 $|y_i|\le H+\delta$ 的范围中，九个坐标各需 $O(1+\log(1+(H+\delta)/\xi))$ 位，再加表示、精度及身份元数据；固定有界 $\delta$ 时可写为每坐标 $O(1+\log(1+H/\xi))$，常数依该固定界。原始传感、量化、数值运算及最终输出误差有各自预算。命题20.5的 dyadic 第一向量整数解码仍可复用，却未为定义29.1的全时间范数／裁剪／幂给出舍入证明。

若额外实际供应一棵 $N=m+n$ 叶的显式代码，三取得状态的叶数分别为

$$
N=m+n,\quad m+2n\le2N,\quad2m+3n\le3N.
$$

它们各有 $2\#\text{叶}-1$ 个节点；字面逐节点求三个向量的叉积数准确为

$$
(N-1)+(m+2n-1)+(2m+3n-1)=4m+6n-3\le6N-3.
$$

证明。位宽由上述格点误差及坐标范围直接得到；这只是条件表示，不把一个准确实坐标称为有限位资源。叶数使用原 $M,M^2$ 的组成，节点与叉积数使用命题13.2及 Process44.9的满二叉结构归纳。这个推论细化命题13.2的较松 $7N-3$ 显式代码上界，不给无代码观察者新端口，也不给外部 Read／$\rho$ 仪器定价。来源 $N$ 无界，两个调用不能证明源侧维护、存储或感测有 $N$ 无关的物理成本。

付费新读协议改变兼容来源纤维，还要计新读宽度、更新、身份与存储；它不是本固定旧记录任务。确定有界误差下复读可以重复同一误差，平均收益需另供随机律。换度量、固定预测终点、限制树大小、增加共同收缩裕量或其它控制菜单都是另一个问题，未用于定理24.2。

## 31. 达到的精确实例 $H_*(6,4)=32/27$

**定理 31.1（全支撑覆盖的有限精确证书）。** 对 $L=6,d_0=4$，有

$$
H_*=32/27,
$$

且在三读最大值恰为此数时已有实际增长来源。

证明。此时 $z=\log2,\ell=\log6$。两个纯叶的最小读数上界均为2。先证较小组成截止 $Q=\varphi^2z/G<80$，使用纯整数不等式

$$
559^2<5\cdot250^2,\qquad2^{103411}>6^{40000}.
$$

它们分别给 $\varphi^2>1309/500$ 及

$$
\log_2 6<\frac{103411}{40000}
=\frac{79}{80}\frac{1309}{500}<\frac{79}{80}\varphi^2.
$$

所以 $G>\varphi^2z/80>0$。约定25.3证明每个可能改善或持平纯叶上界2的实际组成都满足 $m+n\le m+\varphi n\le Q<80$；枚举更宽的 $m+n\le80$ 安全且覆盖全部原树，不给问题加树大小配额。

若混合 $m>n>0$，$f_0=f_2$ 的交点 $v=-nz/m$ 位于 $[-\log3,\log6]$。两条相反斜率的最大值在那里最小，其值为 $(m+n-n^2/m)z>mz\ge2z$；$f_1$ 在交点更小。因此这些组成不能改善2。若 $n\ge m>0$，三个斜率都非负，区间左端 $v=-\log3$ 给最小值。在该端点，同一实际制备的幅度为

$$
q_0=6^m/3^n,\qquad q_1=2^n/3^m,\qquad q_2=q_0q_1.
$$

以下程序只使用准确整数／有理数，完整测试剩余支撑（包括等组成；双偶数被原支撑排除）：

```python
from fractions import Fraction as Q
assert 559**2 < 5*250**2
assert 2**103411 > 6**40000
best=Q(2); minimizers=[]; supported=0
for m in range(1,81):
    for n in range(1,81-m):
        if m%2==0 and n%2==0: continue
        supported += 1
        if m>n:
            assert Q(m+n)-Q(n*n,m)>m
            continue
        q0=Q(6)**m/Q(3)**n
        q1=Q(2)**n/Q(3)**m
        value=max(q0,q1,q0*q1)
        if value<best: best=value; minimizers=[(m,n)]
        elif value==best: minimizers.append((m,n))
assert supported==2380
assert best==Q(32,27) and minimizers==[(3,5)]
print(supported, str(best), minimizers)
```

输出为 `2380 32/27 [(3, 5)]`。有限程序的覆盖由前述截止及实际三线优化证明承担；程序不给有限样本之外的新无限量词。

为给字面实际达到者，令 $k=\langle\beta,\alpha\rangle$，先双左接 $\alpha$，再两轮双左接 $\beta$，得到八叶树

$$
t=\left\langle\beta,\left\langle\beta,\left\langle\beta,
\left\langle\beta,\left\langle\alpha,\left\langle\alpha,
\langle\beta,\alpha\rangle\right\rangle\right\rangle
\right\rangle\right\rangle\right\rangle\right\rangle.
$$

其组成为 $(3,5)$，单位标签为 $-f_3$。在 $p=(6e_1,e_2/3)$ 处，$|a|=6,|b|=1/3,\Delta=4$，字面有序求值及原运输给

$$
\begin{aligned}
x_0&=(0,0,8/9),&x_1&=(-32/27,0,0),\\
x_2&=(0,-256/243,0),&x_3&=(0,0,8192/6561).
\end{aligned}
$$

前三范数准确为 $8/9,32/27,256/243$，最大值 $32/27$。$\Gamma\ge G>0$，故阈值达到者本身增长；定理28.2的小正向旋转对保留全部等号，证明在准确 $H=32/27$ 时每个正记录误差都有无穷全时间距离。仅用叶来源会误将所需读界提高到2。

## 32. 原始来源对应、精确证据及未决边界

**约定 32.1（复用与数学证据的范围）。** 本节的实际对象仍是 Atomic2–3 的非空有序树、原 $\rho$ 及固定叶对的结构解释：本卷定义1.1–1.2直接给该对应；GenealogicalFiberTransport 的 `Source=FreeMagma Bool` 中 true／false 分别对应 $\alpha,\beta$。本卷定理3.1的运输只作解释换参，不执行换制备。Boundary7.2的固定单位标签通过同一有序节点归纳接入本卷定理4.3；Process44.2的组成／单位方向共同像提供真正的双接及根反序来源见证，不由线性张成或边缘计数推定联合实现。

实际恢复前提恰为本卷定理5.1及引理16.2／推论16.3：$x_3=\operatorname{sgn}(x_0\cdot(x_2\times x_1))(x_2\times x_1)$，非零尾有 $q_2\le q_0q_1$ 和归一化三重积绝对值至少 $c$；零标签尾按原描述子及正交运输归零。第25节的 $G=\varphi^2\gamma$、三线判据、紧截止覆盖和阈值达到／未达到与第18–19节逐项相同。正向旋转保持叉积及全部供应约束的证明复用定理17.2；旋转、根反序、正交化与缩放都只准备竞争来源，不成为未知源菜单。第30节只把推论20.3的候选纤维比较接到完整序列，通用最坏恢复方法不计作新的数学发现。

经典叉积基础仍引用 Darpö，*Vector product algebras*，[arXiv:0810.5464v1](https://arxiv.org/pdf/0810.5464v1)，Lemma2及证明；特征不为2、交替双线性积、非退化对称型、循环配对与范数恒等式在原定向正定实三维成立。正输入幂公式可对应 Peter J. Larcombe、Ovidiu D. Bagdasar，*On a Result of Bunder Involving Horadam Sequences: A Proof and Generalization*，*Fibonacci Quarterly* 51(2), 174–176，[原文](https://www.fq.math.ca/Papers1/51-2/LarcombeBagdasarHoradam.pdf)，式(2.2)–(2.3)：取其幂参数 $p=q=1$、$z_n=q_{n+1}$，只在两个初值正的分支使用；该文不承担本卷的实际组成、零／符号分支、平台或端口结论。

[Computational Behavior15](COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md)及 [RankOneInfiniteHorizonRisk](../../../D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.lean) 的严格稳定标量族说明没有共同谱隙时的已知外推机制；其来源为 $a^n$，不能代替第27节的共同实际树／制备桥。[FiniteHorizonPredictionPseudometric](../../../D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.lean) 的有限距离接口可取状态 $\mathcal T\times\mathcal P$、更新 $(t,p)\mapsto(\rho t,p)$、观察 $E_p(t)$、$T=2$，再限制比较的初态到 $\mathcal D$，其域无需更新不变；单独的有界无限距离结论要求整个输出载体的全局距离界，原 $\mathbb R^3$ 及增长行不满足。[NoUniformInfiniteFutureRadius](../../../D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius.lean) 使用无理圆周旋转与 floor 字母读数，来源和观察均不同。读取这些原文不构成本卷新增 Lean 编译证据。

RH_OFFLINE 的增订一·10中复 Fibonacci rapidity，及 Atomic416 的固定算术观察阈值／绝对商块渐近，都没有这里的叶制备和三向量取得假设，不用同名递推或对数尺度充当几何前提。Boundary43 的半径制备／读误差及 Process44 的外部 affine 仪器也保持其独立来源和权限合同。本卷第24–31节是上述准确接口下的普通数学综合推导（`repo-derived`），未主张全球原创性、文献穷尽或新的内核核验。

**约定 32.2（有限精确证据）。** 定理31.1的完整整数／有理数程序给2380个混合支撑组成、唯一最优组成 $(3,5)$ 及准确值 $32/27$；其八叶字面树在原制备下的四向量、根反序取负及前三读上界逐坐标准确成立。规范树 $T_0$ 至 $T_{15}$ 的字面组成和叶数核对 $N_l=F_{l+1}$；在 $\mathbb Q(\sqrt5)$ 中核对 $F_{n+1}-\varphi F_n=\psi^n$，$0\le n\le37$，其中13个 $n\equiv1\pmod3$ 的连续数组成为奇／奇；对应前五个双接字面树保持规定组成及非零第三轴。

另取1–4叶全部102棵有序标签树，在五个正交、非正交、依赖或零叶制备上，准确核对3060个三读恢复式及2040个字面运输实例；正交半单位制备还核对612个非负单项式实例。对 $L=1,H=1/2,d_0=1/16$，准确有理报告核对12834个实例及 $j=3,\ldots,12$ 的128340个未来比较，实际零尾、正确符号、错误符号和计算零符号分别为9250、1008、784、1792个；7322个报告需输入裁剪，28个报告非正交。使用的误差预算是各报告向量真实差的 $\ell^1$ 范数最大值，它是准确的 Euclidean 同时误差上界，不改变主问题的 $d_3$。系数准确为 $K_{\rm err}=17$、全时间充分系数19。非零初值 $x_0=(0,0,-1/5)$ 的实际零尾在 $L=2,H=1/2,d_0=1$ 下另核对125份报告和1250个相同有限时刻比较。

一个额外有理共同实现取 $T_6$、$L=2,H=1,d_0=5/4$，两正交叶长分别为 $(7/4,7/10)$ 与 $(7/4,699/1000)$。其行列式准确为 $2401/1600$、$23941449/16000000$，六个取得范数都不超过1，两个正 $q_1,q_2$ 都严格小于1，记录距离小于 $1/32$；原括号及运输给相同结果。它只核对一个 $d_0>1,H=1$ 的实际收缩对，第27节的无限族与上确界仍由其完整证明承担。

这些有限计算检验准确指标、有限证书覆盖后的枚举和具体报告分支；不是无限全树、任意制备或全时间结论的抽样证明。全称内容由结构归纳、源的联合约束、增长判据、非负单项式估计及第27–28节的实际成对构造承担。

**约定 32.3（仍需单独处理的边界）。** 定理24.2确定完整参数制度、准确零误差、尖锐线性阶、一个明确正区间上的精确单位平台、平台大误差端点及任意正误差的无穷障碍；尚未确定有界制度的完整有限误差曲线、最优线性系数或平台正误差的全部精确风险常数。精确参数阈值是数学存在性决定，其任意实数比较／整数截止的有限位有效决定仍需表示合同。

定义29.1是旧记录的理想运算求值器，不认证任意实数的符号／范数表示、全时间舍入精度、公共域承诺取得、准确制备／动作或物理传感价格。确定同时误差不供应统计复读收益。新的付费读、树码、校准、计数、复制、reset、逆、根交换或旋转菜单，以及不同目标度量或共同收缩裕量均须单独供应，不能作为本原任务已解决的替代物。准确完整未来、语法恢复、原制备反演、同制备上下文拼接与物理空间／时钟／记忆装置的恢复依然是不同关系。

## 追加锚（本行以下为增补区）
## 33. 原参数化树源的精确参考取得

本节及第 34–47 节研究同一实际树历史在不同被动坐标图下的参考取得。共同坐标记录与独立坐标扩展分别陈述；每种取得合同明确给出新增状态、同制备绑定、共观测或保留条件、回复宽度与资源义务。结论覆盖全部非空有序树及全部制备，包括零、平行、反平行、符号与计数分支。精确可识别性、有限取得、条件误差、全时间误差及物理和位资源是不同问题，普通数学证明不宣称 Lean 核验或物理认证。

## 34. 完整来源、记录与目标合同

**定义 34.1（实际来源与历史）。** 令 $\mathcal T$ 为以 $\alpha,\beta$ 为叶的自由有限非空有序二叉树集，构造子记作 $\langle s,t\rangle$。树大小不设上界，不加结合律、交换律、叶识别或空树。原替换为

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
$$

在固定定向欧氏空间 $\mathbb R^3$ 中，一次共同制备 $p=(a,b)$ 给出

$$
E_p(\alpha)=a,\qquad E_p(\beta)=b,\qquad
E_p(\langle s,t\rangle)=E_p(s)\times E_p(t),\qquad
x_j=E_p(\rho^jt).
$$

同一历史中的 $p$ 始终不变。比较世界允许 $p$ 遍历所有向量对，包括零、平行和反平行对；构造比较世界不授予观察者重新制备或主动旋转权限。

**定义 34.2（原取得接口）。** 原调用顺序为

$$
\operatorname{Read},\rho,\operatorname{Read},\rho,
\operatorname{Read},\operatorname{Stop},
$$

对应版本 $t,\rho t,\rho^2t$，原合同使用一个共同坐标图。读取不改变对象；$\rho$ 破坏性覆写唯一来源句柄。取得记录包含精确数值回复、声明的调用顺序，以及不编码来源内容的来源、制备、事件、版本和 Stop 身份。接口不含树代码、计数、叶或地址读出、复制、复位、逆操作、主动旋转、共读探针、运输轴、参考状态，也不含通过费用或耗时编码来源的旁路。描述结构成本的计数不是已观测计数；数值档案不是物理向量档案。

**定义 34.3（独立被动坐标扩展与目标）。** 单独声明世界

$$
w=(t,p,Q_0,Q_1,Q_2),\qquad Q_j\in G,
\qquad G=SO(3)\ \text{或}\ O(3),\qquad y_j=Q_jx_j,
$$

其中三个未知 $Q_j$ 独立且不受额外约束。被动 $Q_j$ 仅将物理向量写成坐标，不改变 $p$、物理叉积或实际树历史。严格未来、当前起未来及包含前缀的目标分别为

$$
F_+(w)=(Q_2x_j)_{j\ge3},\qquad
F_2(w)=(Q_2x_j)_{j\ge2},\qquad
F_0(w)=(Q_2x_j)_{j\ge0}.
$$

目标坐标图是实际最后取得的 $Q_2$，并非一个未指定的未来坐标图。$F_2$ 比 $F_+$ 仅多已取得的 $y_2$；$F_0$ 是另一个任务，不能把它的要求默加到严格未来任务中。

各条件扩展必须给出新增来源或仪器状态、制备和身份绑定、精确共观测或持续保留保证、时序及回复宽度。数学充分性以这些保证为前提；原 Read/$\rho$ 菜单不提供它们，给定校准也不等于已建立物理桥梁。

## 35. 原始全来源闭包、零分支与投影约束

**引理 35.1（解释映射与五符号闭包）。** 记

$$
\begin{aligned}
A&=\|a\|^2,& B&=\|b\|^2,& C&=a\cdot b,& \Delta&=AB-C^2,\\
K&=b\times a,& U&=K\times a=Ca-Ab,& N&=K\times b=Ba-Cb.
\end{aligned}
$$

解释映射 $F(a,b)=(b,K)$ 满足

$$
E_p(\rho^jt)=E_{F^j(p)}(t),\qquad
(A,B,C)\longmapsto(B,\Delta,0).
$$

每棵树有一个普适描述子，形如零或

$$
\varepsilon A^hB^kC^\ell\Delta^dZ,\qquad
h,k,\ell,d\in\mathbb N,\quad \varepsilon\in\{1,-1\},
\quad Z\in\{a,b,K,U,N\}.
$$

**证明。** 两个叶上的解释等式就是两条原替换；有序叉积节点保等式，故结构归纳证明一步，再迭代证明任意 $j$。欧氏叉积恒等式给出 $b\perp K$ 及 $\|K\|^2=\Delta$。完整乘法表为

$$
\begin{aligned}
a\times b&=-K,&a\times K&=-U,&a\times U&=AK,&a\times N&=CK,\\
b\times K&=-N,&b\times U&=CK,&b\times N&=BK,\\
K\times U&=-\Delta a,&K\times N&=-\Delta b,&U\times N&=-\Delta K.
\end{aligned}
$$

对角项为零，逆序项取负。各式由双线性及 $u\times(v\times u)=\|u\|^2v-(u\cdot v)u$ 得到；例如 $K\times(K\times a)=-\Delta a$，展开 $(Ca-Ab)\times(Ba-Cb)$ 得 $-\Delta K$。节点处乘子单项式相乘，再用此表归约，即得描述子的结构归纳。证明不作除法，因而包括 $C=0$ 和 $\Delta=0$；描述子不要求唯一。若 $\Delta=0$，则 $F(p)=(b,0)$、$F^2(p)=(0,0)$，所以即使早期向量非零，也有 $x_j=0$ 对所有 $j\ge2$。$F$ 是解释恒等式，不是可执行的制备操作。证毕。

**定理 35.2（完整尾序列与零边界）。** 取左手单位标架

$$
f_1=e_1,\quad f_2=e_2,\quad f_3=e_2\times e_1,
\qquad \chi(t)=E_{(e_1,e_2)}(t).
$$

$\chi(t)$ 为零或 $\sigma f_i$，其中 $\sigma\in\{1,-1\}$。若 $\Delta>0$，令

$$
r=\sqrt B,\qquad s=\sqrt\Delta,\qquad
 g_1=\frac b r,\quad g_2=\frac K s,\quad g_3=\frac N{rs}.
$$

它们是左手正交单位轴，循环指标满足 $g_{i+1}\times g_i=g_{i+2}$。设实际叶计数为 $\nu(t)=(m,n)$。在 $\chi(t)=\sigma f_i$ 分支中，

$$
\begin{aligned}
x_1&=\sigma r^ms^ng_i,\\
x_2&=\sigma r^ns^{m+n}g_{i+1},\\
q_{j+2}&=q_jq_{j+1},\qquad
x_{j+2}=\sigma(x_{j+1}\times x_j)\quad(j\ge1),
\qquad q_j=\|x_j\|>0.
\end{aligned}
$$

若 $\chi(t)=0$，所有 $x_j$（$j\ge1$）为零。结合 $\Delta=0$ 分支可得

$$
x_2=0\quad\Longleftrightarrow\quad F_2\text{ 全零}
\quad\Longleftrightarrow\quad F_+\text{ 全零}.
$$

**证明。** 五符号表在 $A=B=\Delta=1,C=0$ 时的符号为 $f_1,f_2,f_3,-f_2,f_1$，有限单位标签集对叉积闭合。因此归纳选定的描述子给出非零标签恰在非零描述子且 $\ell=0$ 时。标签为零不要求非正交制备下的 $x_0$ 为零，只要求正交尾部为零。

计数替换为 $M(m,n)=(n,m+n)$，且 $M^2=M+I$。在正交对 $F(p)=(rg_1,sg_2)$ 及后继 $(sg_2,rsg_3)$ 上，双叶齐次性由结构归纳得到前两式。单位标签的循环替换在叶上成立，并由节点叉积保持。$M^2=M+I$ 使后继幅值的每个指数等于前两个指数之和；左手标架乘法和 $\sigma^2=1$ 给出向量递推。轴每三步重复。零标签在任意正交制备上评价为零，故整个尾部为零；$\Delta=0$ 已由引理 35.1 处理。这些分支穷尽全部制备和树。证毕。

**引理 35.3（实际联合来源的投影约束）。** 在非零尾部令 $w=x_2\times x_1=q_1q_2g_{i+2}$，则

$$
\begin{aligned}
P&=\sigma x_0\cdot\frac w{\|w\|}
 =\left(\frac{AB}{\Delta}\right)^h
   \left(\frac sr\right)^m r^n
 =\left(\frac{AB}{\Delta}\right)^h\frac{q_2}{q_1}
 \ge\frac{q_2}{q_1},\\
P&\ge\sqrt{\frac\Delta{AB}}\,q_0,\\
|x_0\cdot(x_2\times x_1)|&\ge q_2^2,\qquad q_2\le q_0q_1.
\end{aligned}
$$

最后两条不等式在零分支也成立。

**证明。** 提取 $\sigma$ 后，初始非零描述子是正单项式乘 $a,b,K,-U,N$ 之一。它们对相应 $g_{i+2}$ 的正投影依次为 $s/r,r,s,s^2/r,rs$；双叶次数依次为 $(1,0),(0,1),(1,1),(2,1),(1,2)$。$A,B,\Delta$ 的次数为 $(2,0),(0,2),(2,2)$。乘法表在每个节点保持次数，描述子的总次数就是实际 $(m,n)$。将正投影按次数合并即得 $P$ 的等式，且 $AB\ge\Delta$。$a,-U$ 的投影与范数之比为 $\sqrt{\Delta/(AB)}$，$b,K,N$ 的该比为一；正标量相消给出第二条。第一条乘 $\|w\|=q_1q_2$ 得标量三重积下界，再由 $P\le q_0$ 得范数约束。零分支有 $w=q_2=0$，无需除法。这里约束的是实际联合来源，并非任意 $\mathbb R^9$ 三元组。证毕。

**定理 35.4（共同坐标解码及正交协变）。** 定义

$$
H(u,v,z)=\operatorname{sgn}\bigl(u\cdot(z\times v)\bigr)(z\times v),
\qquad \operatorname{sgn}(0)=0.
$$

全部实际来源满足 $x_3=H(x_0,x_1,x_2)$；对实际树 $\rho^kt$ 使用原来的 $p$，可用滚动三元组恢复全部未来。任意 $Q\in O(3)$ 满足

$$
H(Qu,Qv,Qz)=QH(u,v,z).
$$

**证明。** 非零分支由引理 35.3 的正投影确定符号；零分支的 $w,x_3$ 均为零。将同一定理用于实际树 $\rho^kt$ 给出逐步迭代。正交变换满足 $(Qu)\times(Qv)=\det(Q)Q(u\times v)$，标量三重积符号也乘 $\det(Q)$，两因子相消，零情形仍成立。故一个未知共同 $O(3)$ 坐标图足够；三个独立坐标报告不满足此应用条件。证毕。

引理 35.1–定理 35.4 复用本卷已发表的第 1.1–1.3、2.1–2.2、3.1、4.1–4.3、5.1 及 16.2–16.3 项。此处完整陈述普通证明，以明确后续取得结论的来源前提。

## 36. 被动与主动反射及全部计数分支

**命题 36.1（主动比较的计数符号）。** 对比较制备 $Rp=(Ra,Rb)$，保留原物理叉积，记 $\delta=\det R$、$L(t)=m+n$，则

$$
E_{Rp}(t)=\delta^{L(t)-1}RE_p(t).
$$

这不同于被动报告 $QE_p(t)$。在不正坐标图中，物理构造子的坐标表达为 $\det(Q)$ 乘坐标标准叉积，因而被动解释对每棵树正是 $QE_p(t)$。

**证明。** 叶上指数为零；节点上两子树指数及新增叉积因子之和为 $L(s)+L(t)-1$，归纳即得。原 $\rho$ 给出 $L_{j+2}=L_j+L_{j+1}$，且 $M^3=I$ 模二。$L_0,L_1,L_2$ 的奇偶性为 $m+n,m,n$，每三步重复。不正主动比较在四种计数奇偶支上的额外符号为

| $(m,n)\bmod2$ | 时间 $0,1,2$ 的符号 |
| --- | --- |
| $(0,0)$ | $(-,-,-)$ |
| $(1,0)$ | $(+,+,-)$ |
| $(0,1)$ | $(+,-,+)$ |
| $(1,1)$ | $(-,+,+)$ |

主动比较下连续三向量行列式的总指数为

$$
(L_j-1)+(L_{j+1}-1)+(L_{j+2}-1)+1=2L_{j+2}-2,
$$

故行列式不变；一个共同被动不正 $Q$ 则使其乘 $\det Q$。这些比较不授予主动操作。证毕。

**命题 36.2（非零标签的精确计数支持）。** 非零单位标签可达的计数恰为两个叶计数 $(1,0),(0,1)$，以及满足 $m,n\ge1$ 且不同时为偶数的计数。反转任一非零内部树的根，得到不同树、相同计数及全部 $x_j$ 的相反值。计数不确定 $\sigma$；叶的 $\sigma=1$。

**证明。** 在 $\mathbb F_2^2$ 中给 $f_1,f_2,f_3$ 分别赋非零次数 $(1,0),(0,1),(1,1)$。非零乘积加次数；同轴乘积为零，故零次数不能对应非零标签。多于一叶的纯标签树含同标签樱桃节点，评价为零。

反之，从 $k=\langle\beta,\alpha\rangle$ 开始，连续两次从左接上 $\alpha$ 或 $\beta$，用垂直单位轴的 $u\times(u\times v)=-v$，保持非零奇/奇标签并使相应计数增加二。因此全部正奇/奇计数可达；再接一枚 $\alpha$ 或 $\beta$，分别得到全部正偶/奇或奇/偶计数，所乘轴不同。这个构造覆盖无界大小。根反转在每次 $\rho$ 下仍是同一有序根分解的反转，叉积反交换给出每个时间的负值。混合支持计数也可能有零树，故支持不保证未知形状的尾部非零。证毕。

## 37. 精确径向像、独立坐标报告像与普适同制备符号对

**定理 37.1（精确报告像）。** 对 $G=SO(3)$ 或 $O(3)$，实际径向像与字面报告像分别恰为

$$
\{(q_0,q_1,q_2)\in[0,\infty)^3:q_2\le q_0q_1\},
\qquad
\mathcal R=\{(y_0,y_1,y_2):\|y_2\|\le\|y_0\|\|y_1\|\}.
$$

**证明。** 必要性是引理 35.3。若 $q_2=0$，取 $t=\alpha$、$a=q_0e_1,b=q_1e_1$，实际三元组为 $(a,b,0)$。这包括不等式允许的每种零／非零组合，特别是 $q_0=0$ 或 $q_1=0$。若 $q_2>0$，记 $h=q_0,k=q_1,l=q_2$，仍取叶 $\alpha$，令

$$
b=ke_1,\qquad a=\frac Ck e_1+\frac lk e_2,
\qquad C=\sqrt{h^2k^2-l^2}.
$$

于是 $(\|a\|,\|b\|,\|b\times a\|)=(h,k,l)$，也包括等号 $C=0$。每个非零物理向量可由一个正旋转送到任意同范数报告，零向量无需选择；三个独立正旋转属于 $SO(3)$，也属于 $O(3)$。上述各组三向量始终来自一个实际历史和同一个 $p$。证毕。

**定理 37.2（每个正可行三元组的同制备反根见证）。** 对所有 $h,k,l>0$ 且 $l\le hk$，存在同一个 $p$ 及计数同为 $(2,1)$ 的两棵实际树，前三个范数为 $(h,k,l)$，全部时间向量互为相反值，单位标签符号也相反。

**证明。** 置

$$
\begin{aligned}
r&=(k^3/l)^{1/5},&s&=(l^2/k)^{1/5},
&C&=\sqrt{h^2r^2/s^2-s^2},\\
b&=re_1,&a&=\frac Cr e_1+\frac sr e_2.
\end{aligned}
$$

因 $s^2/r=l/k\le h$，$C$ 为实数；$r,s>0$，且

$$
B=r^2,\quad\Delta=s^2,\quad A=h^2/s^2,
\quad K=se_3,\quad N=rse_2.
$$

取

$$
t_-=\langle\alpha,\langle\alpha,\beta\rangle\rangle,
\qquad t_+=\langle\langle\alpha,\beta\rangle,\alpha\rangle.
$$

它们有 $\chi(t_-)=-f_2,\chi(t_+)=f_2$。字面评价及五符号表给出

$$
\begin{aligned}
(x_0,x_1,x_2)(t_-,p)&=(U,-BK,-\Delta N),\\
(x_0,x_1,x_2)(t_+,p)&=-(U,-BK,-\Delta N),\\
\|U\|&=\sqrt{A\Delta}=h,
\qquad \|BK\|=r^2s=k,
\qquad \|\Delta N\|=rs^3=l.
\end{aligned}
$$

根反转在全部后来时间仍使值取负，故两符号在同一制备和相同计数上达到，包括 $h=l/k,C=0$ 边界。

三个叶是实现该全称同制备反根要求的最小叶数：叶没有内部根可反转；混合二叶树计数为 $(1,1)$，其 $q_1=rs,q_2=rs^2$ 强迫 $s=l/k,r=k^2/l$，初始 $\|K\|=s$，只能实现 $h=l/k$，纯二叶树尾部为零。五叶 $(3,2)$ 反根对同样可作冗余见证；它不替代这里对全部正三元组的三叶构造。定理 37.1 的叶实现及本定理的三叶负符号树均保留其实际来源意义。证毕。

## 38. 完整达到的未来纤维与取得的充要边界

**定理 38.1（完整未来纤维）。** 固定任意 $y\in\mathcal R$。若 $y_2=0$，$F_+$ 与 $F_2$ 的纤维均是唯一全零序列。若 $q_2=\|y_2\|>0$，记 $z=y_2,q_1=\|y_1\|$，全部实际相容未来恰由下列签名生成：

$$
\begin{gathered}
X_1=v,\qquad X_2=z,
\qquad X_{j+2}=\kappa(X_{j+1}\times X_j)\quad(j\ge1),\\
v\cdot z=0,\qquad\|v\|=q_1,\qquad\kappa\in\{1,-1\}.
\end{gathered}
$$

参数空间是完整达到的 $S^1\times\{1,-1\}$；在实际世界中 $v=Q_2x_1,\kappa=\det(Q_2)\sigma$。

**证明。** 定理 35.2 和正交叉积公式给出包含性。为达到任意 $(v,\kappa)$，在定理 37.2 的共同制备上选择 $\sigma=\kappa$ 的根。把 $(x_1,x_2)$ 送到 $(v,z)$ 的正旋转存在：将两组归一化有序垂直向量各补其标准定向法向，映射所得两个定向正交标架。另独立选正旋转 $Q_0,Q_1$ 把 $x_0,x_1$ 送到给定 $y_0,y_1$。这是一条实际历史，先在 $SO(3)$ 中实现，因而也在 $O(3)$ 中实现；没有将不同边缘世界相乘，也没有新增主动操作。零分支由定理 35.2 处理。证毕。

**定理 38.2（签名取得的充要条件）。** 任意在同一世界上诚实取得的附加记录 $Z$，能由 $(y,Z)$ 恢复全部严格未来，当且仅当非零数据纤维上的 $v$ 和 $\kappa$ 都恒定。零纤维无需这两个量。

**证明。** 递推给出

$$
X_3=\kappa(z\times v),\qquad X_4=q_2^2v,
\qquad
\kappa=\frac{X_3\cdot(z\times v)}{q_1^2q_2^2}.
$$

第二式用 $(z\times v)\times z=\|z\|^2v$。由严格未来可恢复 $v$ 及 $\kappa$，故它们在可解码的数据纤维上必须恒定；反之，取得二者后显示的递推充分。不同签名给出不同未来。只校准 $X_3$ 时，$(v,\kappa)$ 与 $(-v,-\kappa)$ 有相同下一向量及相反 $X_4$；只取符号仍余整个圆，只取方向仍余两个下一向量。证毕。

**命题 38.3（原独立报告的精确不可识别性及条件纤维）。** 三次字面报告能恢复 $F_+$ 当且仅当 $y_2=0$。每个非零实际 $(t,p)$ 即使公开完整 $t,p$，也仍存在同历史圆形障碍；后来任意多次独立未知坐标报告不绑定历史 $Q_2$。

**证明。** 非零完整纤维由定理 38.1 达到。更强地，只将 $Q_2$ 改为 $Q_2P$，其中 $P$ 是固定 $x_2$ 的非恒等正旋转；保留 $Q_0,Q_1,t,p$ 和完整日程。$y_2$ 不变，非零且垂直于 $x_2$ 的 $x_3$ 被移动。后来坐标图可在两世界中全部保持相同，甚至有无穷多次后来报告，所取得报告仍相同而旧 $Q_2$ 下目标不同。若后来通道复用或运输 $Q_2$，那是额外参考合同。

固定非零 $t,p$ 时，$SO(3)$ 中 $\sigma$ 固定，条件纤维恰为一个圆；$O(3)$ 中两个 $\kappa$ 仍均可达，因为有序二轴注册有正和不正补全，关于 $\operatorname{span}(x_1,x_2)$ 的反射固定该二轴而翻转 $x_3$。固定 $p$、树未知时，在固定范数三元组的 $SO(3)$ 纤维中，只要有相容非零内部树，其根反转就实现两符号；若相容树全为叶，则仅有正符号。$O(3)$ 中两种情况都含两 $\kappa$。除叶例外，不能从计数推断树符号。证毕。

## 39. 最大可恢复商、前缀及公开制备的细化

**定理 39.1（尾轨道与最大可识别不变量商）。** 非零未来的范数完全由 $q_1,q_2$ 决定：

$$
q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\quad(j\ge2),
\qquad F_0=0,\ F_1=1,\ F_{n+2}=F_n+F_{n+1}.
$$

$F_2$ 或 $F_+$ 的共同 $O(3)$ 轨道分类为零类或 $(q_1,q_2)$；完整共同 $SO(3)$ 轨道分类还需 $\kappa$。从字面独立报告可识别的最大不变量商，即使允许 $SO(3)$ 不变函数，也只保留该 $O(3)$ 分类。

**证明。** 幅值公式由乘法递推归纳。两两 Gram 项在 $j\equiv k\pmod3$ 时为 $q_jq_k$，否则为零；按时间排序的连续三轴行列式为

$$
\det[X_j,X_{j+1},X_{j+2}]=-\kappa q_jq_{j+1}q_{j+2}.
$$

将一个张成空间的有序三轴标架正交映到另一个，便映射全部尾坐标，故 Gram 决定共同 $O(3)$ 轨道；该映射为正旋转恰在连续行列式相同时。每个非零字面纤维都有两 $\kappa$，可识别函数必须合并这两符号。这不宣称恢复了完整 $SO(3)$ 轨道。证毕。

**定理 39.2（严格未来的最大任意可识别商）。** 最大任意可识别目标商是

$$
J_+=\begin{cases}
\text{零类},&z=0,\\
(z,q_1),&z\ne0.
\end{cases}
$$

严格未来和当前起未来使用同一分类。

**证明。** $y_2$ 与 $\|y_1\|$ 直接给出该商。对任意目标的固定 $q_1,q_2$ 和任意 $h\ge q_2/q_1$，定理 37.2 与定理 38.1 在初始范数 $h$ 上实现该目标。因此所有同 $z,q_1$ 的目标能共处一个字面记录，任何由报告可恢复的未来函数在此类上恒定，必经 $J_+$ 分解。$q_0$ 不能保留，因为它不是 $F_+$ 的函数。反之，非零严格目标自身可区分不同 $J_+$：

$$
q_2=q_4/q_3,\qquad q_1=q_3^2/q_4,
\qquad z=q_2X_5/\|X_5\|.
$$

零目标统一合并。证毕。

**定理 39.3（包含前缀的可识别性与最大商）。** 字面报告恢复 $F_0$ 当且仅当 $q_0=q_1=q_2=0$。最大可识别不变量前缀商为 $(q_0,q_1,q_2)$，最大任意可识别前缀商为 $(q_0,q_1,q_2,X_2)$。

**证明。** 非零尾部已不可识别；若 $q_2=0$，其零报告对 $Q_2$ 无约束，$Q_2$ 可移动非零 $x_0$ 或 $x_1$，不改变 $y_0,y_1,y_2$。若三者均零，定理 35.2 给出整个零历史。

显示的商同时是 $F_0$ 与字面记录的函数。任何两个商相同的实际 $F_0$ 目标可共享 $y_2=X_2$，并独立把 $x_0,x_1$ 旋转到同范数的共同 $y_0,y_1$。所以可恢复函数在该目标类上恒定。对不变量函数，共同改变 $X_2$ 的方向不能有影响，故它经三个范数分解。这是可识别商，不是完整前缀 $O(3)$ 轨道分类：初始 Gram 夹角和定向前缀数据可在同一记录下不同。前缀与未来的零类合并规则不同。证毕。

**命题 39.4（另供精确公共制备时的计数唯一性与例外）。** 若另供精确 $p$ 且 $\Delta>0$，在 $(r,s)\ne(1,1)$ 时，非零 $q_1,q_2$ 唯一确定实际整数计数。叶计数给 $\sigma=1$，内部非零树仍有同制备反根双符号。在 $r=s=1$ 时，叶范数纤维也含双符号。

**证明。** 两计数的差 $d_m,d_n$ 若给同 $q_1,q_2$，则

$$
d_m\log r+d_n\log s=0,\qquad
d_n\log r+(d_m+d_n)\log s=0.
$$

非零整数对的行列式 $d_m^2+d_md_n-d_n^2$ 非零：若 $d_n\ne0$ 而行列式为零，有理数 $d_m/d_n$ 必为无理根 $(-1\pm\sqrt5)/2$；$d_n=0$ 时立即成立。因此非零计数差强迫 $\log r=\log s=0$。非单位 $(r,s)$ 上计数唯一。叶符号为正；其余实际相容非零内部树及反根在同一公共 $p$ 上给双符号，并保持 $q_0$。

在 $r=s=1$ 时，$\alpha$ 的范数三元组 $(\sqrt A,1,1)$ 也由定理 37.2 的 $t_-,t_+$ 在同一 $p$ 给出，因为 $\|U\|=\sqrt{A\Delta}=\sqrt A$。$\beta$ 的 $(1,1,1)$ 也由 $k=\langle\beta,\alpha\rangle$ 及其反根给出，因为 $\|K\|=\|b\|=1$。其它相容内部树自有反根。因此每个非零单位 $(r,s)$ 范数纤维，包括叶纤维，都含双符号。退化 $p$ 的未来则全零。计数唯一性核心复用本卷定理 6.4；它是精确集合层面的结果，不供应有界搜索、有限精度整数识别或计数／校准端口。证毕。

## 40. 扩展全时间距离下的精确固定记录极小极大半径

**定理 40.1（下一向量的两种输出半径）。** 固定非零字面记录，$X_3$ 遍历 $z^\perp$ 中半径 $q_3=q_1q_2$ 的整圆。允许估计器输出任意 $\mathbb R^3$ 向量时，精确最坏极小极大半径为 $q_3$；要求输出相容下一向量时，半径为 $2q_3$。

**证明。** 零中心达到 $q_3$；任意中心面对两个已达到的相反向量，由三角不等式至少有一个误差为 $q_3$。圆上任意相容输出的对径点相容且距离为 $2q_3$，而圆直径也为此值。证毕。

**定理 40.2（完整序列的精确扩展半径）。** 对严格序列使用可取无穷的距离

$$
d_\infty(U,X)=\sup_{j\ge3}\|U_j-X_j\|.
$$

已知锚定余类为 $j\equiv2\pmod3$，此时 $X_j=(q_j/q_2)z$；另外两个余类是半径 $q_j$ 的圆。置

$$
R_\infty=\sup\{q_j:j\ge3,\ j\not\equiv2\pmod3\}\in[0,\infty].
$$

任意序列输出的精确极小极大半径为 $R_\infty$；要求输出一条实际相容完整未来时为 $2R_\infty$。零未来分支的两个半径均为零，包含当前 $X_2$ 不改变它们。

**证明。** 在锚定余类输出精确值，其余输出零，风险为 $R_\infty$。每个未知坐标都有已达到的对径点，任意输出在该坐标的风险至少为 $q_j$，取上确界得到下界，包含无穷及上确界未达到的情形。

相容输出任选一个签名，任意其它目标在未知坐标的距离不超过 $2q_j$，在锚定坐标相同。保持 $\kappa$、改 $v$ 为 $-v$ 是已达到的另一签名，它恰使两个未知余类方向取反而保留锚，距离为 $2R_\infty$。故上、下界相同。证毕。

这些是没有额外校准的固定精确独立坐标记录风险，不是含噪极小极大定理或随机噪声律。对径见证来自定理 37.2 的实际历史，也可用固定历史的 $Q_2$ 半转达到。公式只用既有 Fibonacci 递推，不借用共同坐标下的全时间制度分类；有限视界以相应有限坐标最大值代替上确界。

## 41. 强最终时刻规范库：无需对齐旧坐标的未来取得

**定义 41.1（最终时刻的实际 $b,K,N$ 库）。** 新增持久同制备原生库，其有标签句柄为

$$
c_1=\beta\ (b),\qquad
c_2=\langle\beta,\alpha\rangle\ (K),\qquad
c_3=\langle\langle\beta,\alpha\rangle,\beta\rangle\ (N).
$$

供应者须从实际目标制备另行构造或供应这些句柄，认证共同制备及句柄／版本身份，使它们免受目标 $\rho$ 的覆写，并将物理值保持到最终观测。这是新增辅助状态与供应，不是目标复制、叶访问或原 Read 返回的矩阵。标签与共观测属于付费合同。目标仍有三次时间顺序报告、两次更新；仅在时刻二，以原子或明确规定的最终回复，在同一实际 $Q_2$ 中共观测当前目标及所需参考句柄。无需早期参考或 $Q_0,Q_1$ 对齐。

在 $SO(3)$ 中，额外取得 $u=Q_2b,w=Q_2K$ 两个向量；含原九坐标共十五实坐标。在 $O(3)$ 中，再取得 $n=Q_2N$，共三个额外向量、十八实坐标；也可用两向量加另行取得且认证的最终定向位 $\det(Q_2)$，为十五实坐标加一位。该位的认证、绝对定向参考、状态、初始化、时刻绑定和物理价格都是额外义务，不能由两个向量猜出。

**定理 41.2（全来源的最终库充分性）。** 定义 41.1 的 $SO(3)$ 两探针或 $O(3)$ 三探针／定向位合同恢复全部严格未来，无须对齐旧坐标或取得过去向量。

**证明。** 若 $z=y_2=0$，直接输出零未来，不作归一化、求逆、轴或符号决定。此时库可退化，统一回复合同仍良定义。若 $z\ne0$，定理 35.2 给 $\Delta>0,r,s>0$。探针范数给 $r=\|u\|,s=\|w\|$。在 $SO(3)$ 中计算

$$
h_1=u/r,\qquad h_2=w/s,\qquad h_3=(w\times u)/(rs).
$$

这恰是 $Q_2g_1,Q_2g_2,Q_2g_3$。在 $O(3)$ 三探针合同中使用 $h_3=n/(rs)$；因

$$
\det[b,K,N]=-B\Delta<0,\qquad
\delta=\det Q_2=-\operatorname{sgn}\det[u,w,n],
$$

可取得真实被动图定向。定向位替代中令 $h_3=\delta(w\times u)/(rs)$。六个实际带符号轴中恰有一个 $\ell\in\{1,2,3\}$ 和 $\sigma\in\{1,-1\}$ 满足 $z=\sigma q_2h_\ell$；正交单位标架及 $q_2>0$ 保证唯一。定理 35.2 的 $x_2$ 位于带符号轴 $i+1$，故取循环指标

$$
v=\sigma q_1h_{\ell-1},\qquad
\kappa=\delta\sigma\quad(\delta=1\text{ 在 }SO(3)\text{ 中}).
$$

所得正是 $Q_2x_1$ 和正确图内递推符号。定理 38.1–38.2 于是恢复严格未来，包括其第一项。只需已取得的旧范数 $q_1$；没有共观测过去向量、揭示树或计数、执行制备映射 $F$ 或对齐 $Q_0,Q_1$。全部零、符号及大小分支均已处理。该库对未来目标充分，不自动恢复 $a,b$ 或前缀。证毕。

**定理 41.3（特定有标签库子集的尖锐必要性）。** 仅在定义 41.1 的特定库子集、且没有其它端口的菜单中，全来源完整未来在 $SO(3)$ 中至少需两个参考回复，在 $O(3)$ 中无定向数据时至少需三个。

**证明。** 在 $SO(3)$ 中任意一个参考都失败，即使有 $z$。取单位 $p=(e_1,e_2)$、$k=\langle\beta,\alpha\rangle$，使 $x_1$ 平行所选库轴的实际内部树可取

| 所选参考 | 实际树 | 单位标签 |
| --- | --- | --- |
| $b$ | $\langle k,\langle k,\alpha\rangle\rangle$（五叶） | $-f_1$ |
| $K$ | $\langle k,\alpha\rangle$（三叶） | $-f_2$ |
| $N$ | $k$（二叶） | $f_3$ |

第一尾方向由这些标签直接给出，全部幅值为一。第一世界的 $Q_2$ 取恒等；第二世界反根，并将 $Q_2$ 取绕所选物理库轴的正半转。参考不变，负 $x_2,x_3$ 被转回而匹配，但平行于固定轴的 $x_4$ 仍相反。独立正 $Q_0,Q_1$ 匹配前两报告。因此一个参考甚至能匹配下一向量，仍不足以恢复完整未来。定理 41.2 给两参考充分性。

在 $O(3)$ 中，任选两个库向量，关于其物理张成平面作反射。保持单位 $p$ 和同一棵树，并使 $x_2$ 位于已含轴：$\alpha$ 有 $x_2=K$，$\beta$ 有 $x_2=N$，$k$ 有 $x_2=b$，每个二探针对至少能选一个。被动末图反射固定两参考和 $z$，而未来循环访问遗漏正交轴，彼处向量不同。$t,p,Q_0,Q_1$ 均不变。三探针充分性见定理 41.2。这些实际来源反例证明限定菜单的二／三回复界；它们不是维数启发，也不是任意编码、标量或物理测量端口的下界。证毕。

## 42. 保留实际末图：恰需两次后续读取与更新

**定义 42.1（实际 $Q_2$ 的前瞻保留）。** 新增仪器状态须在第三报告的坐标图丢失前、且在 Stop 前，前瞻或原子绑定该报告实际使用的 $Q_2$。它保证指定的随后目标 Read 使用这个保留图，$\rho$ 仅改变目标。确认、坐标图／来源／事件身份、参考保留及成本均需记录。该状态不返回免费轴或矩阵；未保留的历史图消失后不能追溯安装。

**定理 42.2（两次额外 Read 与两次额外 $\rho$ 的充分性）。** 在定义 42.1 菜单中，原第三报告若有 $z=0$，可在 $\rho^2t$ Stop 并输出零未来。非零时，保留 $Q_2$，执行一次 $\rho,\operatorname{Read}$ 取得时间三，再执行一次取得时间四，最后在 $\rho^4t$ Stop，即可恢复严格未来。

**证明。** $X_2,X_3,X_4$ 位于同一图。可在实际移位树上使用定理 35.4 的 $H$ 并迭代；也可计算

$$
v=X_4/q_2^2,\qquad
\kappa=\operatorname{sgn}\bigl(X_3\cdot(z\times v)\bigr).
$$

该标量的绝对值为 $q_1^2q_2^2>0$，故给出精确符号，定理 38.2 解码从时间三起的未来，包括已读取的 $X_3,X_4$。没有来源逆操作。非零日程共五次对象向量 Read、十五实坐标、四次 $\rho$，另计新增参考状态；未对齐前缀不随之恢复。证毕。

**定理 42.3（每个非零纤维的限定菜单下界）。** 定义 42.1 菜单中，每个非零字面纤维至少需两次额外向量 Read，且至少需两次额外 $\rho$ 更新，才能恢复完整严格未来。允许唯一额外 Read 在策略选择的任意晚但有限时刻，仍不能突破读取下界。

**证明。** 令 $u=z/q_2,d=X_3/q_3$。纤维可写为

$$
X_j=\begin{cases}
q_ju,&j\equiv2\pmod3,\\
q_jd,&j\equiv0\pmod3,\\
q_j\kappa(d\times u),&j\equiv1\pmod3.
\end{cases}
$$

所有垂直于 $u$ 的单位 $d$ 及两 $\kappa$ 均由定理 37.2 的同制备构造和正注册达到。唯一额外读取前，确定历史策略只见同一字面记录，故在比较世界中选择相同时间 $J$。若 $J\equiv2$，取同 $\kappa$、不同 $d$；若 $J\equiv0$，取同 $d$、相反 $\kappa$；若 $J\equiv1$，取 $(d,\kappa)$ 和 $(-d,-\kappa)$。唯一回复各自相同，完整目标却在另一余类不同。无读策略也失败，所有动作、状态及 Stop 可共用不编码来源的身份元数据；同版本重复读不增信息。

若最多一次额外更新，无论多少读取，只能取得 $X_2,X_3$，上述 $J\equiv0$ 对匹配二者而 $X_4$ 相反。定理 42.2 恰用两更新及两新值达到。下界仅属该菜单，不是来源执行、运行时或任意端口的最优性结论。证毕。

**推论 42.4（限定输入独立随机化仍不能单读全解）。** 输入独立随机策略若至多一次额外向量读且有限停止，并且策略／随机种子事件及成功事件可测，则不可能对每个世界几乎必然精确成功。

**证明。** 在固定字面记录上，按唯一读取的三种余类或无读取分割种子空间，四类之一有正概率。独立于实际种子，固定定理 42.3 给该类的已达到比较对。类中每个种子的两条完整记录相同而目标不同，算法不能同时正确；两个固定世界的错误概率之和至少为该类概率。因此不能逐世界几乎必然成功。结论不涉及输入相关种子、不可测策略、无限停止、期望读取预算或近似风险。证毕。

有限取得期间保留 $Q_2$，足以产生数学坐标及对全部后来指标的精确有限求值器。若要与后来物理设备比较，须另给后来时刻的物理参考保留合同，求值器本身不提供它。

## 43. 三时刻与过去校准：不同规范库及精确退化

**定义 43.1（三时刻参考合同）。** 参考库在第一次目标报告前安装，在各实际 $Q_j$ 中与目标共观测。共同制备真实性、标签、免受目标 $\rho$ 影响、持续保持及同时刻绑定均为付费前提。目标仍在 $\rho^2t$ Stop，但返回比最终时刻未来库更多的数据。以下严格区分所供物理向量：规范库供 $b,K$（$SO(3)$）或 $b,K,N$（$O(3)$）；制备库供 $a,b$（$SO(3)$）或 $a,b,K$（$O(3)$）。不能在两菜单间默换探针。

**定理 43.2（三时刻 $b,K,N$ 规范库的精确过去范围）。** $SO(3)$ 的 $b,K$ 库增加六向量回复，共二十七实坐标；$O(3)$ 的 $b,K,N$ 库增加九回复，共三十六实坐标。它们对全部来源恢复未来；恢复 $F_0$ 的范围为 $\Delta>0$，或 $\Delta=0,b\ne0$，或已经全零的前缀。在 $b=0,a\ne0$ 分支，除 $t=\alpha$ 外全部树的完整历史为零，故成功；$t=\alpha$ 则失败。

**证明。** 当 $\Delta>0$，$O(3)$ 库的真列矩阵

$$
A_j=[Q_jb,Q_jK,Q_jN]
$$

可逆，并有 $A_2A_j^{-1}=Q_2Q_j^{-1}$。$SO(3)$ 两探针构造的正交三轴也有同一相对运输性质。对齐 $y_0,y_1$ 并加 $y_2$ 后，用定理 35.4 恢复未来，已对齐档案给出 $F_0$。即使 $\chi(t)=0$ 或 $x_2=0$，此结论仍成立，因为参考秩属于 $p$，不属于特定目标尾部。两探针加另付费的相对奇偶标志也能恢复 $O(3)$ 运输：过去校准需到时刻二的两条链路各一标志，或各时刻独立认证 $\det(Q_j)$ 的三位；这不同于仅最终时刻的一位变体。

当 $\Delta=0,b\ne0$，$a$ 为 $b$ 的倍数，所有内部叉积消失，全部来源值在 $\operatorname{span}b$ 上。$b_j=Q_jb$ 非零，对每个过去报告的精确对齐值为

$$
\frac{y_j\cdot b_j}{\|b_j\|^2}\,b_2.
$$

它包括 $a=0$、平行及反平行叶，恢复所需向量而不宣称恢复全环境矩阵。若 $a=b=0$，所有值为零。

最后给出完整边界反例：取 $b=0,a\ne0,t=\alpha$。字面替换给

$$
x_0=a\ne0,\qquad x_1=x_2=0,\qquad
b=K=N=0.
$$

全部三个时刻的规范参考都为零。固定 $Q_0,Q_1$，取两个移动 $a$ 的不同正 $Q_2$；每个扩展回复、标签、制备／版本记录及日程均相同，$F_0$ 却已在 $Q_2a$ 处不同。因而该菜单不能对所有制备恢复过去。本卷命题 6.5 和命题 11.3 给同一实际零叶边界：$b=0,a\ne0$ 时，其它树均全零，只有 $\alpha$ 留非零初值。全部来源的未来充分性仍由定理 41.2 保持，不能由零未来推断取得了非零过去的定向；也未增加 $a$ 探针。证毕。

**定理 43.3（三时刻 $a,b,K$ 制备库的全制备前缀恢复）。** 定义 43.1 的另一个菜单，供 $a,b$（$SO(3)$）或 $a,b,K$（$O(3)$），对全部制备及全部树恢复 $F_0$，含零、平行、反平行及 $b=0,a\ne0$。回复数量仍为六／九额外向量和二十七／三十六实坐标，但供应状态不同。

**证明。** 若 $\Delta>0$，$a,b$ 独立。将 $a$ 归一化，去掉 $b$ 沿 $a$ 的分量并归一化，再用定向叉积补全，所得 $SO(3)$ 三轴矩阵满足 $D_j=Q_jD_{\rm native}$，故

$$
D_2D_j^{\mathsf T}=Q_2Q_j^{-1}.
$$

在 $O(3)$ 中取 $P_j=[Q_ja,Q_jb,Q_jK]$，由 $\det[a,b,K]=-\Delta\ne0$ 得 $P_2P_j^{-1}$ 为精确运输。只用两叶探针加独立定向位时，用 $\det(Q_j)$ 乘由前两轴导出的叉积，取得物理法向；三位变体为二十七实坐标加三位，相对奇偶标志则提供对应两链路变体。

若 $\Delta=0$，从 $a,b$ 中按精确探针范数选择一个有标签的非零物理参考 $r$。它在每个时刻的 $r_j=Q_jr$ 非零，全部来源值在 $\operatorname{span}r$ 上。以

$$
\frac{y_j\cdot r_j}{\|r_j\|^2}\,r_2
$$

对齐；两叶全零时直接用零。这包括 $b=0,a\ne0$ 时选 $a$，因而证明全制备 $F_0$，无逆来源操作或零处分母。恢复的是实际直线上的值，不是唯一三维图运输。

两个 $a,b$ 探针独自仍非完整 $O(3)$ 解：单位 $p$、$t=\beta$ 有 $x_2=N=e_1$ 位于叶平面，关于该平面的最终被动反射固定两叶和 $z$，却翻转后来 $K$ 轴向量。这是同来源实际反例，同时适用于未来和前缀。因此本菜单需要第三物理法向或付费定向数据。证毕。

叶制备库的物化宽度可不同于规范库：两枚一叶状态与一、二、三叶状态不是同一供应。二者均非免费公共 $p$ 或物理可供应性宣告。最终时刻规范库、三时刻规范库、全制备叶库及完整过去对齐保留各自目标与资源条件；未来任务不要求更宽的过去消费者。

## 44. 前瞻物理输出记忆与共读替代合同

**定义 44.1（两枚实际物理输出槽）。** 在前两次原读取时，把实际物理 $x_0,x_1$ 捕获到两个新增且有身份的物理向量槽。认证其目标／来源／制备／版本关联，在目标经历 $\rho$ 时保留物理值。这是新物理输出记忆状态，旧数值记录 $y_0,y_1$ 不提供它们。最终时刻在实际 $Q_2$ 中同时共观测两槽与当前目标，返回 $Q_2x_0,Q_2x_1,z$；必须在该图丢失前绑定同一个瞬时 $Q_2$，即使旧数值 Read 使用不同图。两次捕获、两物理槽、保存、标签、身份认证及最终共读都收费；目标仍两次更新后在 $\rho^2t$ Stop。

**定理 44.2（完整共读及收缩回复）。** 完整合同对 $SO(3)$ 或 $O(3)$ 的全部制备恢复未来和数值前缀。额外两向量回复，即最终多六实坐标，总发出十五实坐标。只为未来可改供 $v=Q_2x_1$ 加符号位

$$
\kappa=\operatorname{sgn}\bigl((Q_2x_0)\cdot(z\times v)\bigr)
\quad(z\ne0),
$$

在 $z=0$ 时供任意固定二值位。

**证明。** 完整回复是共同图中的实际来源三元组，定理 35.4 的 $H$ 与迭代恢复 $F_+$，共观测槽直接给数值前缀。理想槽状态有六个实坐标自由度，这个描述不推出设备或位成本。

非零尾部的显示符号恰为 $\det(Q_2)\sigma$，定理 38.2 解码未来；零尾部不需符号或归一化。收缩回复额外宽度为三实坐标加一位，但传感器仍须拥有两个实际捕获输出、同时 $Q_2$ 绑定及身份保证，因此不证明更便宜的捕获／存储硬件。它不返回 $Q_2x_0$，自身不能解决前缀恢复。另供直接目标方向加符号位传感口，须再明确声明该测量合同，原 Read/$\rho$ 不推出它。

未保留的 $x_0,x_1$ 不能由数值记录在本合同下追溯捕获；物理槽替代既不是目标复制／复位，也不是未计价的档案运输矩阵。证毕。

## 45. 条件误差、有限视界与全时间障碍

**命题 45.1（有秩裕量的条件运输误差）。** 设真共同参考列矩阵 $P_j$ 的最小奇异值至少为 $\mu>0$，真运输

$$
T=P_2P_j^{-1}=Q_2Q_j^{-1}
$$

为正交矩阵。令 $\widehat P_j=P_j+E_j$，两时刻算子误差均不超过 $e<\mu$，且 $\widehat T=\widehat P_2\widehat P_j^{-1}$，则

$$
\widehat T-T=(E_2-TE_j)(P_j+E_j)^{-1},
\qquad D:=\|\widehat T-T\|_{\rm op}\le\frac{2e}{\mu-e}.
$$

若真目标范数不超过 $H$、报告误差不超过 $\delta$，则对齐误差不超过 $DH+(1+D)\delta$。三列各自直接测量误差不超过 $\eta$ 时，可取 $e\le\sqrt3\eta$。

**证明。** 将差式右乘 $P_j+E_j$ 得分子恒等式；$\|(P_j+E_j)u\|\ge(\mu-e)\|u\|$ 给逆范数界，且 $\|T\|_{\rm op}=1$。将对齐差拆成 $(\widehat T-T)x$ 与 $\widehat T$ 乘报告误差，得到后一个界。列误差用 Frobenius 范数控制算子范数。结论仅是有秩条件的有限记录结果，并不对全部制备统一成立。证毕。

**命题 45.2（导出叉积列的误差与局部轴识别）。** 在 $SO(3)$ 中，若真叶范数不超过 $L$、个别测量误差不超过 $\eta$，由测得叶形成原始列 $[a,b,a\times b]$ 时，第三列误差不超过 $2L\eta+\eta^2$，可取

$$
e\le\sqrt{2\eta^2+(2L\eta+\eta^2)^2}.
$$

对原始规范列 $[b,K,K\times b]$，用 $\|b\|,\|K\|$ 的各自上界之和替代 $2L$。最终库带符号轴分类在每个固定非零真世界局部稳定，但全来源上不提供统一裕量。

**证明。** 展开 $(a+e_a)\times(b+e_b)-a\times b$，三个误差项的界分别为 $L\eta,L\eta,\eta^2$，再合成三列的 Frobenius 界。规范列同理。在 $O(3)$ 中，这种导出第三列不被默认为共观测物理法向；须有 $SO(3)$ 前提或另付费定向信息。归一化矩阵须另算其诱导误差，不能把原始列误差直接当成归一化误差。定向位错误不属显示的矩阵误差合同，除非另给界。

固定非零世界的六代表 $\pm q_2h_\ell$ 两两距离至少 $\sqrt2q_2$，同轴异号距离为 $2q_2$。若目标扰动不超过 $\epsilon$，以相同精确幅值 $q_2$ 构造的扰动轴代表误差不超过 $q_2\eta_{\rm axis}$，且

$$
\epsilon+q_2\eta_{\rm axis}<q_2/\sqrt2,
$$

则最近轴分类不变：真代表距离至多左侧，错误代表距离至少 $\sqrt2q_2$ 减左侧。幅值也带误差时，在此差异界另加 $|\widehat q_2-q_2|(1+\eta_{\rm axis})$，因为扰动轴范数不超过 $1+\eta_{\rm axis}$；若扰动轴另归一化为单位，幅值项仅为 $|\widehat q_2-q_2|$。$r,s>0$ 处归一化连续，$O(3)$ 库真行列式绝对值 $B\Delta>0$，故足够小的局部探针误差也保持定向。

这些裕量为正但依世界而定；全来源的 $r,s,q_2$ 可趋零，无统一秩或符号裕量。精确 $z=0$ 测试不因此成为含噪零／符号 oracle。噪声、标签、参考／制备身份、定向及共观测前提均需计价。证毕。

**命题 45.3（复用两种不同来源域的含噪下一向量界）。** 保持原制备与 $\rho$ 准确，先在共同坐标下取得实际三元组，三个同时向量读误差均不超过 $\zeta$。在本卷定义 16.1 的主域 $\mathcal D_{L,H,d_0}$，即

$$
\|a\|,\|b\|\le L,\quad \Delta\ge d_0,
\quad 0<d_0<L^4,\quad q_0,q_1,q_2\le H,
\qquad c=\sqrt{d_0}/L^2,
$$

本卷定理 20.2 给

$$
\|H(\text{含噪三元组})-x_3\|
\le\frac4c(H^2+2H+\zeta)\zeta.
$$

在不同的、更宽的定义 21.1 域 $\mathcal D_H$，允许全部制备且只要求 $q_0,q_1,q_2\le H$，本卷推论 21.4 给

$$
\begin{aligned}
\text{误差}&\le b_\zeta+2H\sqrt{p_\zeta},\\
b_\zeta&=(2H+\zeta)\zeta,\qquad
p_\zeta=H^2\zeta+(H+\zeta)b_\zeta.
\end{aligned}
$$

**证明。** 叉积误差至多 $b_\zeta$。主域上引理 35.3 的真投影至少 $c\|x_0\|$：若 $\|x_0\|<2\zeta$，实际 $q_2\le q_0q_1$ 控制目标幅度；否则将标量误差界除以 $\|x_0\|$，并用 $\|x_0\|+\zeta\le3\|x_0\|/2$。错误或计算为零的符号分支给

$$
c\|x_0\|\|x_2\times x_1\|
\le H^2\|x_0\|\zeta+\tfrac32\|x_0\|b_\zeta,
$$

合成即得主域系数；正确符号、真零及计算零分支包含在内，无须精确含噪符号 oracle。

较宽域没有统一 $c$。符号错误或为零时，普适三重积下界给 $q_2^2\le p_\zeta$，故 $\|x_2\times x_1\|\le H\sqrt{p_\zeta}$；同符号或零目标仅需叉积误差界。若三元组经含噪校准对齐，先将命题 45.1 的对齐界合成为同时 $\zeta$，再应用满足实际域前提的那一定理。这些复用结论不成为新校准噪声最优性。证毕。

**命题 45.4（实际平方根尖锐对的完整见证）。** 较宽 $\mathcal D_H$ 上，下一向量模量与固定三读完整误差球风险具有平方根最坏阶；见证保留原括号和同一联合来源限制，不反驳固定 $L,d_0$ 的主域线性界。

**证明。** 复用本卷定理 21.3，完整构造如下。固定 $h_0,h_1\in(0,H)$，取足够小 $s>0$，在正定向标准标架置

$$
\begin{gathered}
r=\sqrt{h_1/s},\quad B=r^2,\quad\Delta=s^2,\quad
C=\sqrt{h_0^2h_1/s^3-s^2},\\
b=re_1,\qquad a=(C/r)e_1+(s/r)e_2.
\end{gathered}
$$

选定理 37.2 的字面 $t_-$，得

$$
x_0=(s/r)(-se_1+Ce_2),\quad x_1=-h_1e_3,
\quad x_2=-qe_2,\qquad q=rs^3=\sqrt{h_1}s^{5/2}.
$$

令 $\theta=2\arctan(s/C)$，另构造实际制备和反根树

$$
\begin{gathered}
b'=r(\cos\theta e_1+\sin\theta e_2),\qquad K'=-se_3,\\
N'=rs(\sin\theta e_1-\cos\theta e_2),
\qquad a'=(C/B)b'+N'/B,\qquad t'=t_+.
\end{gathered}
$$

$K'\times b'=N'$、$b'\perp N'$ 及 $b'\times(K'\times b')=BK'$ 给 $b'\times a'=K'$；两制备有相同 $A,B,C,\Delta$。半角恒等式

$$
\cos\theta=\frac{C^2-s^2}{C^2+s^2},\qquad
\sin\theta=\frac{2Cs}{C^2+s^2}
$$

给

$$
U'=\frac{CN'-\Delta b'}B=(s/r)(se_1-Ce_2)=-U,
\quad x'_0=x_0,\quad x'_1=x_1,
\quad x'_2=q(\sin\theta e_1-\cos\theta e_2).
$$

两范数三元组均为 $(h_0,h_1,q)$，所以同时在 $\mathcal D_H$。记录距离与下一目标差精确为

$$
\begin{aligned}
\varepsilon_s&=2q\sin(\theta/2)=2s^5/h_0,\\
\|x_3-x'_3\|&=2h_1q\cos(\theta/2)
=\sqrt2\,h_1^{3/2}\sqrt{h_0}\sqrt{\varepsilon_s}\cos(\theta/2).
\end{aligned}
$$

这由平面单位向量弦长公式及实际相反符号得到：$x_3=-(x_2\times x_1)$、$x'_3=x'_2\times x'_1$，并非任意环境符号假设。$s\downarrow0$ 时 $\cos(\theta/2)\to1$，且 $\varepsilon_s$ 参数化每个足够小正距离，给完整小误差平方根下界；本卷定理 21.2 给匹配上界。记录距离 $2\zeta$ 的实际对共用中点含噪回复，本卷推论 20.3 的纤维论证给匹配风险下界。

该对的叶范数 $\|a\|=h_0/s,\|b\|=\sqrt{h_1/s}$ 发散，$\Delta=s^2\to0$，因此不属于任意固定 $L,d_0$ 主域。两成员各是实际树／制备，不是任意环境数据，也不授予根反转或主动制备操作。证毕。

**命题 45.5（原制备移位窗口与有限视界误差）。** 若原精确 $q_0,q_1,q_2\le H$，保留三元组 $X_2,X_3,X_4$ 的幅值界可取 $H'=\max(H,H^2,H^3)$。移位窗口定理的来源是实际树 $\rho^kt$ 配同一个原 $p$，因此叶界和 $\Delta$ 仍是原值，无须将它们强加到仅作解释的 $F^2(p)$。

**证明。** $q_3=q_1q_2\le H^2$、$q_4=q_2q_3\le H^3$。若 $\kappa$ 已认证，带符号叉积迭代的误差 $e_j=\|\widehat X_j-X_j\|$ 由双线性展开满足

$$
e_{j+2}\le q_{j+1}e_j+q_je_{j+1}+e_je_{j+1}.
$$

符号未认证时则需在每个移位实际三元组上使用适用的 $H$ 域界。两方法均需真范数与累计误差账目，均只给有限视界结论，常数可随视界增长。证毕。

**命题 45.6（有限精确取得不推出统一全时间含噪保证）。** 原实际来源含一对初始有限记录可任意接近、未来扩展上确界差为无穷的合法制备；添加固定有限原生参考库或实际输出捕获记录仍不消除此障碍。

**证明。** 复用本卷命题 22.1：取 $t=\alpha,p=((3/2)e_1,(3/2)e_2)$，属于 $L=2,H=4,d_0=1$ 主域，且

$$
q_j=(3/2)^{F_{j+1}}.
$$

另一个固定制备由绕 $e_3$ 的小非零正旋转得到。初始三报告随角趋零而接近，$x_2$ 固定；循环 $e_1,e_2$ 方向的未来差为

$$
2\sin(\theta/2)(3/2)^{F_{j+1}},
$$

上确界无穷。每个固定原生参考及捕获／读取向量在正旋转下协变，范数有限；固定有限整组记录的扰动随角趋零，全部定向位可保持相同。因此有限精确恢复不提供统一全时间上确界误差保证，即使已声明有限校准库。这里比较的是全来源的合法制备对，不是准许观察者执行主动旋转。本命题不增加全参数全时间分类、校准噪声最优性或固定位数承诺。证毕。

## 46. 联合资源与精确实数限制

**约定 46.1（同一实现的资源向量）。** 成本保留为多坐标量：实际目标制备／供应与活树存储，目标 $\rho$ 执行，每个取得回复及宽度，事件／时间／Stop／来源／制备身份，辅助库或物理槽供应及维护，坐标图／定向参考状态和认证，原始数值档案，紧凑预测器及临时空间，每个有限请求输出，以及精度／算术／运行时。没有一个共同标量价格证明各合同中的物理赢家。

各合同的同时回复与更新资源为：

| 合同 | 额外取得及状态 | 含原报告的坐标总数 | 目标更新 |
| --- | --- | --- | --- |
| 原共同图或独立图三读 | 三个原对象向量回复；独立图恢复边界见第 38.1–38.3 项 | 九实坐标 | 二次 |
| 最终时刻 $b,K$／$b,K,N$ 库 | 二／三参考回复；持久同制备原生状态与最终共观测 | 十五／十八实坐标 | 二次 |
| 最终时刻 $O(3)$ 两探针加定向位 | 两回复及认证绝对定向、初始化与时刻绑定 | 十五实坐标加一位 | 二次 |
| 保留实际 $Q_2$ 的非零日程 | 两次后续对象回复；有限仪器参考保留 | 十五实坐标 | 四次 |
| 三时刻 $b,K$／$b,K,N$ 库 | 六／九参考回复；每时刻同制备共观测及相对参考义务 | 二十七／三十六实坐标 | 二次 |
| 三时刻 $a,b$／$a,b,K$ 制备库 | 同回复数量，供给不同物理状态；退化直线回退 | 二十七／三十六实坐标 | 二次 |
| 前瞻物理输出槽完整共读 | 两新增向量槽、两捕获、保持、最终共读；额外六坐标 | 十五实坐标 | 二次 |
| 物理槽的收缩未来回复 | 同捕获与传感义务；额外三坐标及一符号位 | 十二实坐标加一位 | 二次 |

三时刻 $O(3)$ 两探针定向替代须另计两个相对链路标志或三个逐时刻认证位。零未来可在原三读／二更新后停止，但所声明的参考供应状态不能因此免费。回复宽度不代替制备、保持、认证或硬件费用；这些是可分别选择的数学合同，物理实施未由本卷建立。

**命题 46.2（精确预测器与不同档案义务）。** 精确校准后签名 $(v,z,\kappa)$ 有六个实坐标及一个符号，$q_1=\|v\|$。每个有限输出可用固定维数滚动临时空间、每步一次带符号叉积计算；请求输出存储与原档案分别计价。

**证明。** 定理 38.1 的二向量递推给滚动求值；零分支使用零。签名是预测器，不替代必须保留的原始档案和身份。一个有限精确求值器表示无限序列，不能有限时间打印无限坐标。

若在另一个合同中明确供应来源代码，原叶计数 $(m,n)$ 给 $L_2=2m+3n,L_4=5m+8n$，完整二叉树有 $2L_j-1$ 节点；这些由计数替换直接得到，不从原 Read 揭示计数，也不在缺少表示模型时定价物理 $\rho$。证毕。

**命题 46.3（精确实数与位承诺的边界）。** 任意实坐标、受保护符号判定、归一化和除法都是数学操作，不自动给有限位实现。固定非零字面记录上的不可数圆不能由有限或可数附加字母表精确区分。

**证明。** 若每个圆上目标都精确可识别，附加记录在不同目标间必须不同；否则定理 38.2 失败。不可数集不能单射到可数集，所以该字母表不能使所有目标纤维成为单点。这只是信息障碍，不是近似位下界。

本卷命题 20.5 的条件 dyadic $H$ 解码，在仪器供应 dyadic 坐标与同时精度承诺、总误差不超过一的合同中，需固定次数整数运算，分子宽度

$$
B_{\rm num}=O(1+b+\log(1+H)),
$$

学校算法位工作 $O(B_{\rm num}^2)$、临时位 $O(B_{\rm num})$，$b$ 为二进制小数精度。该既有有限下一向量结果不定价新库中的平方根／除法／参考生产或无界未来增长。有效界、量化、来源／制备／动作误差、坐标漂移、传感误差律、认证及有限视界数值预算须各自供应。资源陈述不隐藏逆、复制、复位或来源码端口。证毕。

## 47. 来源映射、成熟结果的假设及保留边界

**约定 47.1（本卷内的准确复用位置）。** 来源、解释、尾部及共同图闭合来自本卷第 1–5 节；实际联合像、根反转、退化及计数纤维来自第 6.1–6.5 项；实际尾像和二值区别来自第 7 节；制备及零档案边界来自第 11.1–11.3 项；资源、操作及文献限制来自第 13–15 节；投影来自第 16.2–16.3 项；计数支持来自定义 18.1；含噪下一向量与 dyadic 解码来自定理 20.2、命题 20.5、定理 21.3 和推论 21.4；实际增长尾障碍来自命题 22.1。第 24–32 节的共同图全时间结论保留其来源域、制度及数值／资源条件，不提供免费的跨图校准。

第 35–36 节给出后续所用的原来源普通证明；第 37 节给精确报告像及同制备反根见证；第 38 节给全部达到的未来纤维与取得充要条件；第 39–40 节给不同目标商和精确记录风险；第 41–44 节分别给最终库、保留末图、三时刻不同库及物理槽合同；第 45–46 节给条件误差与共同资源。全称结论依赖这些证明，不依赖有限样本枚举。

**约定 47.2（仓内运输与读取结果的实际前提）。** 下列路径的结果只在其原假设下适用；它们不从原向量 Read/$\rho$ 菜单产生参考状态。

| 仓内真源路径 | 复用位置及条件 |
| --- | --- |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md` | 第 19.10–19.12 项区分不变量记录、协变输出、种子条件及实际联合记录纤维分解，前提是目标在实际联合纤维上恒定；第 20.7 项的同来源 XOR 校准位是另行取得变量；第 20.9 项区分被动坐标运输与物理移动／事件记录。纤维分解不取得缺失数据。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md` | 第 11 节假设有类型的运输映射、路径／相干及分辨率数据。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md` | 第 40 节假设 transition cocycle 及实际像／拼接条件。 |
| `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md` | 第 347、397 节运输联合事件／规范数据，开放路径有端点标架及 holonomy 义务；无已观测关系时不能推断标架。 |
| `docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md` | 第 377 节另给群、表示、运输、二胞及测度，不由原 FIB 语法供应原生参考句柄。 |
| `docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md` | 第 19 节给 $SO(3)$ 边运输与权重；第 44 节使用不同的 $W=E$ 加 $H$ 仪器、严格球冠和明确操作／制备菜单，不能当成本卷原接口权限。 |
| `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean` | `FreeMagma Bool` 来源中 `true` 对应 $\alpha$，有替换／计数、单射和谱系组成纤维；不供应向量评价校准或物理逆操作。 |
| `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean` | 使用带地址的 $\alpha$／$\beta$／分支／缺席四符号读取及有限 frontier 回退，是不同于原向量 Read 的端口。 |
| `D5/S3/Observer/AgencyHolonomy/MemoryTransport.lean` | 组合已经给定的记忆映射。 |
| `D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.lean` | 假设已经给定可见环路数据。 |
| `D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion.lean` | 假设已经给定群系数及全局标架拼接数据。 |
| `Library/Geometry/darpo2009vectorproduct.md` | 区分相容向量积恒等式／分类与完整 $SO(7)$ 协变，区分反事实控制字识别与一条实际历史取得；这里不借用七维或解析可逆控制定理。 |
| `Library/Geometry/singerwu2011vectordiffusion.md` | 假设加权正交边块、反向转置对称；流形近似另需局部 PCA／切标架采样条件。这里不借用流形极限或图估计定理。 |

此表前五个理论路径与五个 D5／两个 Library 路径对应修订 `29b8128bae35565e814eba59541bd28934aa64ac` 的相关完整节或模块；几何卷第 19、44 节及本卷第 1–23 节对应修订 `55c7d475f0367a2c7cc3989dedefad8e4552a04e` 的已发表正文。来源定位不等于重新编译这些 Lean 模块；本卷没有从它们冒领已形式化的参考取得定理。

**约定 47.3（主要文献的窄适用映射）。** Horn，*Closed-form solution of absolute orientation using unit quaternions*，JOSA A 4 (1987)，629–642，[作者原 PDF](https://people.csail.mit.edu/bkph/papers/Absolute_Orientation.pdf)，第 1.B、2.A 节的精确三轴构造要求已知对应非共线点和正旋转。本卷原点共同、尺度一，有标签 $(0,a,b)$ 或 $(0,b,K)$ 恰在 $\Delta>0$ 时非共线。第 38.1、41.2、43.2–43.3 项的正三轴证明明确满足这些条件；$O(3)$ 须有实际第三法向或认证定向。这里不借用其最小二乘估计器或统计性能。

Villar 等，*Scalars are universal: Equivariant machine learning, structured like classical physics*，[arXiv:2106.06610v2](https://arxiv.org/pdf/2106.06610v2)，第 5–6 页引理 1–2 描述同时有限向量组的 $O(d)$ Gram 不变量与 $SO(d)$ 的 Gram 加 $d$ 维子行列式。本卷 $d=3$，一个张成空间的尾三元组由递推决定全部余项，秩零分支另行处理；第 39.1 项的直接有限标架论证核对其前提，并不把三个独立变换报告当作一个共同群作用，也不借用无限输入或学习／近似定理。一般多项式协变、流形／连接一致性、向量积分类和 Kabsch 统计最优性均非这里的依据。

欧氏叉积、轨道／稳定子、注册及纤维分解是复用的成熟关系。本卷新增的实际独立报告纤维、固定记录目标商与半径，以及来源绑定的有限取得合同，是这些关系在原树源上的具体推导，不以重命名协变主张新意，也不主张全局数学原创。有限算术只能检查指定实例、发现反例；定理 37.2、41.3、43.2 和命题 45.4 已给所需完整实际见证及其普通证明。物理可供应性、误差／硬件实验、有限位与形式核验不是这些证明的结论。

**约定 47.4（未决的不同义务）。** 原接口的非零独立图不可识别性保持不变；各扩展的数学充分性以其新增端口、实际来源／制备绑定及同图取得为条件。物理库／槽／参考供应，前瞻 $Q_2$ 保留与共观测认证，校准噪声律、精度及成本认证，任意端口的最优资源价格和新的 Lean 形式化仍是分别未建立的义务。普通证明不等于连续物理空间、时钟或记忆装置的识别，也不将关系表达的长期目标判为完成。

## 追加锚（本行以下为增补区）

## 48. 实际成对来源的方向比较与分别闭合的八元数切面

**定义 48.1（声明载体上的原三读合同）。** 固定 $L,H>0$、$0<d_0<L^4$，置 $\kappa=\sqrt{d_0}/L^2\in(0,1)$，即推论16.3的 $c$。分别取 $V=\mathbb R^3$ 的原定向叉积，或约定2.3的正定实除八元数虚部 $V=\operatorname{Im}\mathbb O$ 及 $u\times v=(uv-vu)/2$。来源仍为定义1.1的全部非空有限有序树及定义1.2的一个固定叶对 $p=(a,b)$；树大小无统一上限，每个来源的所有叶出现和全部时刻使用同一 $p$。实际更新仍为 $(t,p)\mapsto(\rho t,p)$，且

$$
\begin{gathered}
x_j=E_p(\rho^jt),\qquad
\Delta=|a|^2|b|^2-(a\cdot b)^2,\\
\mathcal D^V_{L,H,d_0}
=\{(t,p)\in\mathcal T\times V^2:
|a|,|b|\le L,\ \Delta\ge d_0,\ |x_j|\le H\ (0\le j\le2)\}.
\end{gathered}
$$

两成员分别满足全部限制，允许不同树、不同制备及不同二生成切面。置 $w=x_2\times x_1$、$w'=x'_2\times x'_1$、$e_j=|x_j-x'_j|$，保留原目标 $x_3$ 和原记录距离 $\max_{0\le j\le2}e_j$。记

$$
\omega_V(\varepsilon)=
\sup_{\substack{(t,p),(t',p')\in\mathcal D^V_{L,H,d_0}\\
\max_{0\le j\le2}e_j\le\varepsilon}}|x_3-x'_3|,
\qquad \varepsilon\ge0,
$$

空上确界取零。三维时这就是定义16.1的域与模量。

取得仍按约定1.3及13.1–13.3：三次完整向量 Read、两次破坏性 $\rho$，归档原三读及来源／时间／动作／Stop 身份；回复宽度、保留记录、程序、运算、精度、时间及源成本分别保留。七维载体每次回复七个环境坐标，三读共21个精确实坐标。数学切面坐标不作为已取得校准，也不提供三坐标回复或相同资源价格；原合同不增加树码、Gram／符号口、外部向量输入、复制、复位、逆、旋转或重制备权限。第33–47节中各参考取得扩展另需其声明的新增端口、状态、同图绑定或持续保留条件，不为本合同免费提供校准或这些权限。

**定理 48.2（初始读数与尾叉积的分别灵敏度）。** 对定义48.1任一声明载体上的每个实际来源对，

$$
\begin{aligned}
|x_3-x'_3|
&\le H^2 e_0+\frac{|w-w'|}{\kappa}\\
&\le H^2 e_0+\frac{H}{\kappa}(e_1+e_2).
\end{aligned}
$$

因而

$$
\omega_V(\varepsilon)\le
\min\{2H^2,C_{\rm dir}\varepsilon\},
\qquad C_{\rm dir}=H^2+\frac{2H}{\kappa}.
$$

三维中该充分系数严格小于定理17.1的充分系数：

$$
K_*-C_{\rm dir}
=H^2\left(\frac2\kappa-1\right)
+2H\left(1+\frac1\kappa\right)>0.
$$

这比较两个充分界，不确定最优系数、实际模量的严格下降或任意非实际报告的恢复风险。

证明。三维直接复用定理4.3、5.1及引理16.2。七维先在每个来源内使用约定2.3和 [Boundary定理8.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) 的二生成闭包。其经典依据为 Baez 的 [两生成结合性](https://math.ucr.edu/home/baez/octonions/node2.html) 和 [虚部叉积](https://math.ucr.edu/home/baez/octonions/node14.html)，以及 [Darpö文献注](../../../Library/Geometry/darpo2009vectorproduct.md) 所引定义与Lemma2（这些中间工具为 literature-attested）。由于 $\Delta>0$，可在证明中将 $a$ 归一化，并将 $b$ 的垂直分量归一化为两个正交单位虚元 $e,f$；它们生成 $\operatorname{span}\{1,e,f,ef\}$ 的四元数代数，其虚部为

$$
U_p=\operatorname{span}\{a,b,b\times a\}.
$$

固定一个保内积及叉积的线性等距同构 $J_p:\mathbb R^3\to U_p$，令 $\widetilde p=(J_p^{-1}a,J_p^{-1}b)$。按原有序节点的结构归纳，对全部字面树及全部 $j\ge0$ 同时有

$$
E_p(\rho^jt)=J_pE_{\widetilde p}(\rho^jt).
$$

所有 $F^j(p)$ 也留在此切面，运输仍只是定理3.1的等式。没有重排叉积括号；四元数乘法结合不使叉积结合。该固定同构保留叶 Gram 数据、每次响应范数和来源内的投影，故引理16.2及准确符号公式逐来源适用。另一个来源使用自己的 $J_{p'}$，不把两组坐标中的差当作环境向量差；以下比较全在共同 $V$ 的内积与叉积中进行。

对非零尾，写 $q_j=|x_j|$、$u=w/|w|$、$x_3=\sigma w$，其中 $\sigma\in\{\pm1\}$。复用引理16.2的两个投影界，并保留投影本身，得

$$
P=\sigma x_0\cdot u>0,\qquad
P\ge\kappa q_0,\qquad
|w|=q_1q_2\le q_1^2P\le H^2P.
$$

若任一尾为零，定理5.1使其目标为零；若两非零尾符号相同，目标差等于 $|w-w'|$。这些分支均满足所列界，因为 $\kappa<1$，且不对零向量归一化。

余下两符号相反，交换来源名使 $\sigma=+1,\sigma'=-1$。记

$$
\begin{gathered}
r=|w|,\quad s=|w'|,\quad
u=w/r,\quad v=w'/s,\quad d=|u-v|\le2,\\
P=x_0\cdot u>0,\quad P'=-x'_0\cdot v>0,\quad
S=P+P',\quad R=r+s,\quad b_0=|w-w'|.
\end{gathered}
$$

分别沿 $u$ 和 $v$ 展开 $S$，Cauchy–Schwarz 给

$$
\begin{aligned}
S&=(x_0-x'_0)\cdot u+x'_0\cdot(u-v)
\le e_0+q'_0d,\\
S&=(x_0-x'_0)\cdot v+x_0\cdot(u-v)
\le e_0+q_0d.
\end{aligned}
$$

由两个投影下界，$\min(q_0,q'_0)\le(q_0+q'_0)/2\le S/(2\kappa)$。同时两个幅度界给 $R\le H^2S$，所以

$$
S\left(1-\frac d{2\kappa}\right)\le e_0,
\qquad R\le H^2S.
$$

环境欧氏几何给

$$
b_0^2=(r-s)^2+rsd^2,\qquad
b_0^2-\frac{R^2d^2}{4}
=(r-s)^2\left(1-\frac{d^2}{4}\right)\ge0.
$$

因此 $Rd/2\le b_0$。若 $d\le2\kappa$，因 $1-d/(2\kappa)\ge0$，有

$$
R\left(1-\frac d{2\kappa}\right)
\le H^2S\left(1-\frac d{2\kappa}\right)\le H^2e_0,
$$

于是 $R\le H^2e_0+Rd/(2\kappa)\le H^2e_0+b_0/\kappa$。若 $d\ge2\kappa$，直接有 $b_0\ge Rd/2\ge\kappa R$。两个分支都包括 $d=2\kappa$，不除以可能为零的差因子。异号目标差为 $|w+w'|\le R$，第一界成立。

两个载体均有全局双线性和 $|z\times y|\le|z||y|$；七维中此界由正定八元数叉积范数恒等式给出，即使 $z,y$ 属不同切面也成立。因此

$$
\begin{aligned}
|w-w'|
&\le|(x_2-x'_2)\times x_1|
+|x'_2\times(x_1-x'_1)|\\
&\le H(e_2+e_1).
\end{aligned}
$$

每个实际目标范数又为 $|w|\le H^2$；取原实际成对上确界得到模量界，含零记录距离和空上确界。严格系数比较由代入定理17.1的 $c=\kappa$ 得到。本方向比较及其原来源载体对应为 repo-derived；二生成闭包、配对及范数恒等式只作已有中间工具，不需要共同切面或全 $SO(7)$ 等变。

**命题 48.3（尾记录相同的实际异号对）。** 在三维中取正向正交单位基 $\mathbf e_1,\mathbf e_2,\mathbf e_3$，令 $L=2,H=1,d_0=1/1024$，故 $\kappa=1/128$。两个实际来源

$$
(t,p)=\bigl(\alpha,(\mathbf e_1/32,\mathbf e_2)\bigr),\qquad
(t',p')=\bigl(\langle\alpha,\langle\alpha,\beta\rangle\rangle,
(\mathbf e_3/8,2\mathbf e_1)\bigr)
$$

均属于主域，且其字面连续历史为

$$
\begin{aligned}
(x_0,x_1,x_2,x_3)
&=(\mathbf e_1/32,\mathbf e_2,-\mathbf e_3/32,\mathbf e_1/32),\\
(x'_0,x'_1,x'_2,x'_3)
&=(-\mathbf e_1/32,\mathbf e_2,-\mathbf e_3/32,-\mathbf e_1/32).
\end{aligned}
$$

所以 $w=w'=\mathbf e_1/32$，$e_1=e_2=0$，初始读数差 $e_0=|x_0-x'_0|=1/16$，目标差 $|x_3-x'_3|=1/16$。这两个差在该实例中数值相等；$e_0$ 始终按定义48.1指初始读数差，不以目标差定义。定理48.2的方向界在此取等号；对这组固定参数，任一在全主域成立的界 $|x_3-x'_3|\le A_0e_0+B_0|w-w'|$ 必须有 $A_0\ge1$，不由此确定 $C_{\rm dir}$ 的最优性。

证明。第一叶对有 $\Delta=1/1024$，第二叶对有 $\Delta'=1/16$；全部叶范数不超过2，所列前三向量范数不超过1。第二来源的原括号求值为 $a\times(a\times b)$，按定理3.1依次在

$$
F^jp'=(\mathbf e_3/8,2\mathbf e_1),\ (2\mathbf e_1,-\mathbf e_2/4),\
(-\mathbf e_2/4,\mathbf e_3/2),\ (\mathbf e_3/2,\mathbf e_1/8)
\quad(0\le j\le3)
$$

求值，得到所列四向量；第一来源是叶，直接求原连续替换得所列结果。两尾叉积和目标差随即成立；代入 $w-w'=0$ 给 $A_0\ge1$。这是原来源的投影灵敏度见证，不是环境三元组、噪声报告或付费控制的反例。

## 追加锚（本行以下为增补区）

## 49. 来源、取得及表示合同

本文固定非空有限自由有序二叉树、原定向三维叉积及同一次执行中共享的叶对。主要结论是一个平方范数多项式求值核：有一致收缩证书时，它以有限记录和有限计算控制整个未来；在两个单位平台上，具有统一有限位上限的完整记录的统一误差下确界为 $1/2$，但该端点不能达到；在三个增长制度中，甚至任意逐源有限、长度无统一上界的记录也不能保证任何有限统一绝对误差。精确有理回复和另行供应的可细化名字具有不同的正结果。全文是普通数学证明；有限算术核对只用于检出实例、索引和程序错误，没有新的 Lean 或内核验证。

来源语法为 $t::=\alpha\mid\beta\mid\langle s,t\rangle$，左右次序与全部括号保留。对一个实际固定叶对 $p=(a,b)\in(\mathbb R^3)^2$，定义

$$
E_p(\alpha)=a,\quad E_p(\beta)=b,\quad E_p\langle s,t\rangle=E_p(s)\times E_p(t),
\qquad \rho\alpha=\beta,\quad\rho\beta=\langle\beta,\alpha\rangle.
$$

$\rho$ 保持节点。记 $x_j=E_p(\rho^jt)$、$q_j=|x_j|$。实际取得固定为

$$\operatorname{Read}(x_0);\ \rho;\ \operatorname{Read}(x_1);\ \rho;\ \operatorname{Read}(x_2);\ \operatorname{Stop}.$$

目标始终是同一共同坐标系中全部 $j\ge3$ 的向量，以 $\sup_{j\ge3}|\widehat x_j-x_j|$ 计误差。停止后的当前源是 $\rho^2t$。没有树码、计数、叶读取、校准、复制、重置、逆动作或进一步源读口。构造竞争来源时的旋转、缩放、根反序与已知树生成，只用于证明，不增加未知源的动作。

传感器和生产者必须共同保证九个有限整数 $n_{ik}$、公共有限整数 $b\ge0$ 所表示的 $y_{ik}=n_{ik}2^{-b}$ 满足 $|y_i-x_i|\le e$，$i=0,1,2$。误差可以相关、对抗并依赖历史；不假设平均可以改善它。准确准备与准确 $\rho$ 是模型前提，不能把动作或准备误差偷换成读误差。程序使用的 $\bar H,\rho,c_-,\kappa,E$ 等均为有限有理数及其有效证书；数学上的任意实参数比较不是可执行分类器。证书文字、校验成本、发行依据和身份另计。

“完整记录”包括全部源相关程序、元数据、建议和选择信息。统一有限位上限意味着它只有有限种取值；每源有限而长度无界意味着至多可数种取值。任意实数寄存器和可细化无限名字不属于这两个合同。动作、读时刻、坐标系、源版本和 Stop 身份的合法记录也计费，身份不得夹带隐藏大小、树码或源相关建议。

## 50. 实际三锚、投影和多项式核

置 $A=|a|^2,B=|b|^2,C=a\cdot b,\Delta=AB-C^2$，$K=b\times a$、$U=K\times a=Ca-Ab$、$V=K\times b=Ba-Cb$。运输 $F(a,b)=(b,K)$ 满足 $E_p(\rho^jt)=E_{F^jp}(t)$：两个叶直接成立，节点用双线性结构归纳，随后对 $j$ 归纳。它只是解释换参。

以下五符号表、尾递推和三读符号恒等式复用本卷引理 4.2、定理 4.3、5.1；此处 $U,V$ 对应原表的 $L,N$，$F$ 对应定理 3.1 的解释运输。给出其关系是为了固定求值核的参数，不将这些经典恒等式或已发表证明计为新数学。完整上三角叉积表为

| $\times$ | $b$ | $K$ | $U$ | $V$ |
|---|---|---|---|---|
| $a$ | $-K$ | $-U$ | $AK$ | $CK$ |
| $b$ | | $-V$ | $CK$ | $BK$ |
| $K$ | | | $-\Delta a$ | $-\Delta b$ |
| $U$ | | | | $-\Delta K$ |

同向项为零，反序取负。逐项由重复向量恒等式及上述 $U,V$ 展开验证；例如 $U\times V=-\Delta K$。因此每树有对全部准备同时有效的零描述子，或 $\epsilon A^uB^vC^h\Delta^wZ$，$Z\in\{a,b,K,U,V\}$。在单位叶 $(e_1,e_2)$ 处，令 $f_1=e_1,f_2=e_2,f_3=e_2\times e_1$，单位标签 $\chi(t)$ 为 $0,\pm f_i$。表归纳说明标签非零恰是所选描述子无正 $C$ 因子且非零；其初始方向依次为 $\sigma(a\text{ 或 }V)$、$\sigma(b\text{ 或 }-U)$、$\sigma K$，各乘正单项式。

若 $\Delta>0$，$r=\sqrt B,s=\sqrt\Delta$，$g_1=b/r,g_2=K/s,g_3=V/(rs)$ 是左手正交单位标架。树的组成 $(m,n)$ 为两种实际叶数。对 $\chi(t)=\sigma f_i\ne0$，齐次性和运输给

$$x_1=\sigma r^ms^ng_i,\quad x_2=\sigma r^ns^{m+n}g_{i+1},\quad
q_{j+2}=q_jq_{j+1},\quad x_{j+2}=\sigma(x_{j+1}\times x_j)\quad(j\ge1).$$

因为组成更新矩阵 $M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 满足 $M^2=M+I$，每个幅度指数满足该递推；标架叉积表给方向。标签零时 $F(p)$ 已正交，全部 $j\ge1$ 为零，但 $x_0$ 可非零；$\Delta=0$ 时 $F^2p=0$，全部 $j\ge2$ 为零。

令 $w=x_2\times x_1$。初始五符号中 $a\cdot V=\Delta$、$(-U)\cdot b=\Delta$，其余相应内积为正范数平方，故

$$x_3=\operatorname{sgn}(x_0\cdot w)w,\qquad\operatorname{sgn}(0)=0.$$

零及依赖分支 $w=0$ 仍成立。将此式应用于每个实际替换后树，三次准确读决定完整未来。

以下投影恒等式与无除法不等式复用本卷引理 16.2、推论 16.3；其五符号次数证明覆盖全部实际树。它们是实际像中的量化约束，不能给环境三元组强加它。给 $A,B,C,\Delta$ 双次数 $(2,0),(0,2),(1,1),(2,2)$，给 $a,b,K,U,V$ 双次数 $(1,0),(0,1),(1,1),(2,1),(1,2)$。表保持次数。非零标签写 $x_0=\sigma A^uB^v\Delta^w Z$、$Z\in\{a,b,K,-U,V\}$。对应单位正投影依次为 $s/r,r,s,s^2/r,rs$，恰为 $(s/r)^{m_Z}r^{n_Z}$。因此，$\widehat w=w/|w|$ 时

$$\sigma x_0\cdot\widehat w=(AB/\Delta)^u q_2/q_1\ge q_2/q_1,
\qquad \sigma x_0\cdot\widehat w\ge\sqrt{\Delta/(AB)}q_0.$$

后式由五个方向的投影/范数比分别为 $\sqrt{\Delta/(AB)},1,1,\sqrt{\Delta/(AB)},1$ 得到。退化分支两边归零。于是所有实际来源都有

$$|x_0\cdot w|\ge q_2^2,\quad q_2\le q_0q_1;\qquad
\Delta\ge d_0,\ |a|,|b|\le L\Longrightarrow |x_0\cdot w|\ge c q_0|w|,\quad c=\sqrt{d_0}/L^2.$$

若三读均不超过 $H$，又有 $|w|=q_1q_2\le H^2q_0$。

令 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$。对 $j\ge3$，置 $a_j=F_{j-2},b_j=F_{j-1}$。归纳给 $q_j=q_1^{a_j}q_2^{b_j}$，并把向量写成非负三锚式：相位 $1,2,0$ 分别为

$$q_1^{a_j-1}q_2^{b_j}x_1,\quad q_1^{a_j}q_2^{b_j-1}x_2,\quad q_1^{a_j-1}q_2^{b_j-1}x_3.$$

所有出现的指数非负，约定 $0^0=1$；依赖分支中 $x_3=0,q_2=0$，后两个相位亦由正 $q_2$ 次数消为零。$F_n\bmod2$ 的状态 $(F_n,F_{n+1})$ 从 $(0,1)$ 经 $(1,1),(1,0)$ 返回，故周期三。于是对任意有限报告，取

$$Z=\operatorname{sgn}(y_0\cdot(y_2\times y_1))(y_2\times y_1),\quad U_y=|y_1|^2,V_y=|y_2|^2,$$

得到统一执行核

$$P_j(y)=\begin{cases}
U_y^{(a_j-1)/2}V_y^{b_j/2}y_1,&j\equiv1\pmod3,\\
U_y^{a_j/2}V_y^{(b_j-1)/2}y_2,&j\equiv2\pmod3,\\
U_y^{(a_j-1)/2}V_y^{(b_j-1)/2}Z,&j\equiv0\pmod3.
\end{cases}$$

这些指数全为非负整数，报告为实际准确值时 $P_j=x_j$。除三锚的有限符号比较外，核在 $y_1,y_2$ 中总次数为 $F_j$。不需要平方根、归一化、裁剪或真实范数端口；平方根只用于证明其误差。

## 51. 所有准备的稳健第三锚

**定理 51.1。** 若 $q_0,q_1,q_2\le\bar H$ 且同时 $|y_i-x_i|\le e$，则

$$|Z-x_3|\le B_e+2\bar H\sqrt{P_e},\qquad B_e=(2\bar H+e)e,\quad P_e=\bar H^2e+(\bar H+e)B_e.$$

证明。双线性给 $|y_2\times y_1-w|\le B_e$。真实尾零或报告符号正确时误差至多 $B_e$。符号错误或报告标量零时，两标量异号或后者为零，故

$$q_2^2\le|x_0\cdot w|\le|x_0\cdot w-y_0\cdot(y_2\times y_1)|\le e|w|+(q_0+e)B_e\le P_e.$$

于是 $|w|\le\bar Hq_2\le\bar H\sqrt{P_e}$，而反号误差至多 $B_e+2|w|$。这覆盖极小向量、零计算结果、错误符号、非正交及不在实际像中的报告。

取 $\bar H\ge1,e\le1$，令 $P=3\bar H^2+3\bar H+1$、$C_s=2\bar H+1+2\bar HP$。有 $P_e\le Pe$、$B_e\le(2\bar H+1)e$，$\sqrt P\le P$，所以 $|Z-x_3|\le C_s\sqrt e$。当 $\bar H=1$，更紧的 $3e+2\sqrt{7e}\le9\sqrt e$ 可用。

**定理 51.2。** 在有条件域 $|a|,|b|\le L,\Delta\ge d_0>0$，供应 $0<c_-\le c$，$e\le1$ 时，同一核满足

$$|Z-x_3|\le C_ce,\qquad C_c=4(\bar H^2+2\bar H+1)/c_-.$$

证明。只须考虑符号错误分支。若 $q_0<2e$，$|w|\le\bar H^2q_0$ 给误差 $\le4\bar H^2e+B_e$。若 $q_0\ge2e>0$，投影下界及 $|w|\le\bar H^2q_0$ 给

$$c_-q_0|w|\le e|w|+(q_0+e)B_e\le\bar H^2q_0e+\tfrac32q_0B_e.$$

因此 $2|w|+B_e\le2\bar H^2e/c_-+(3/c_-+1)B_e\le4(\bar H^2e+B_e)/c_-$，即所列界。$e=0$ 由准确公式承担。该线性结论与无行列式下界的平方根结论是不同条件。

## 52. 无行列式下界的一致收缩与整个尾部

**定理 52.1。** 供应有限有理数 $\bar H\ge1,0\le\rho<1$，所有实际准备满足 $q_0\le\bar H,q_1,q_2\le\rho$；无叶范数、行列式或角度下界。对每个有理 $E>0$，同一多项式核给一个有限报告、有限工作空间的全未来解码器。

令 $R=(1+\rho)/2$，$K_s=C_s+R/(1-R)^2$，并要求

$$e\le e_*:=\min\{1,(1-\rho)/2,(E/(2K_s))^2\},\qquad \xi_{out}\le E/2.$$

选择有限整数 $T\ge0$ 使 $R^T\le E/2$，取最小 $J\ge3$ 使 $F_J\ge T$。$3\le j<J$ 执行 $P_j$ 后舍入；全部 $j\ge J$ 输出零。

证明。$|y_1|,|y_2|\le R$，$|Z|\le R^2$。对两个长度 $n$ 的非负乘积，逐因子替换给差 $\le nR^{n-1}e$，因为范数的误差至多 $e$。相位1、2的标量次数为 $n=F_j-1$，真锚范数至多 $R$；相位0的次数为 $n=F_j-2$，真锚至多 $R^2$。锚误差分别为 $e,e,C_s\sqrt e$。将乘积差乘真锚，再将报告系数乘锚差，得到每相位误差至多

$$C_s\sqrt e+nR^ne\le\left(C_s+\sum_{n\ge1}nR^n\right)\sqrt e=K_s\sqrt e.$$

这直接证明较宽来源域上的多项式核误差，不靠把有条件结论移植过来。有限头部加输出舍入至多 $E$。对于整个无界尾部，准确实际幅度满足

$$q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\le\rho^{F_j}\le R^{F_j}\le R^T\le E/2\qquad(j\ge J).$$

$F_j$ 在 $j\ge3$ 单调，故这是一条全尾证明。$R<1$ 使有理乘法搜索 $T$ 终止；Fibonacci 加法搜索 $J$ 亦终止。$\rho=0$ 直接包含全零分支。

若另外供应 $c_-$，把 $K_s\sqrt e$ 换成 $K_c e$，其中 $K_c=C_c+R/(1-R)^2$，并取 $e_*\le E/(2K_c)$，得到线性精度预算，仍用同一个无范数执行核。所有原线性制度均能接入：$L<1$ 时树范数由叉积范数不等式至多 $L^{\#叶}\le L$；其余线性行 $H<1$ 已给 $q_1,q_2\le H$。实际供方必须给一个有效有理上界 $\rho<1$；此事实不供应免费的任意实数比较。

**平方根率的已发表实际见证。** 下述成对构造复用本卷定理 21.3；这里验证它在 $q_0$ 仅有界、$q_1,q_2$ 一致收缩的较宽域内仍成立。 当 $0<\rho<1$ 时，固定 $0<h_0<\bar H,0<h_1<\rho$，取小 $s>0$，$r=\sqrt{h_1/s}$、$C=\sqrt{h_0^2h_1/s^3-s^2}$，$b=re_1,a=(C/r)e_1+(s/r)e_2$。直接算得 $K=se_3,V=rse_2$；实际树 $t=\langle\alpha,\langle\alpha,\beta\rangle\rangle$ 的三式为 $U,-BK,-\Delta V$，给

$$x_0=(s/r)(-se_1+Ce_2),\quad x_1=-h_1e_3,\quad x_2=-qe_2,\quad q=\sqrt{h_1}s^{5/2}.$$

取 $\theta=2\arctan(s/C)$、$b'=r(\cos\theta e_1+\sin\theta e_2)$、$K'=-se_3$、$V'=rs(\sin\theta e_1-\cos\theta e_2)$、$a'=(C/B)b'+V'/B$，并用根反序树 $t'=\langle\langle\alpha,\beta\rangle,\alpha\rangle$。直接用半角公式验证两个 Gram 相同、$U'=-U$，故 $x'_0=x_0,x'_1=x_1,x'_2=q(\sin\theta e_1-\cos\theta e_2)$。三读距离为 $\epsilon_s=2s^5/h_0$，第三未来距离为 $\sqrt2h_1^{3/2}\sqrt{h_0}\sqrt{\epsilon_s}\cos(\theta/2)$。两源均满足 $q_0=h_0,q_1=h_1,q_2=q<\rho$，而 $\epsilon_s$ 覆盖全部充分小的正数。共同中点报告给平方根风险下界。两叶范数发散、$\Delta\to0$，故不能反驳有条件域的线性界。

## 53. 完整十制度及真实达到阈值

定义原参数域 $\mathcal D_{L,H,d_0}$ 为所有实际来源满足 $|a|,|b|\le L,\Delta\ge d_0$ 及 $q_0,q_1,q_2\le H$，$L,H>0,0<d_0<L^4$。令 $d_3=\max_{i\le2}|x_i-x'_i|$、$d_\infty=\sup_{j\ge3}|x_j-x'_j|$、$\Omega(\epsilon)=\sup_{d_3\le\epsilon}d_\infty$。置

$$\varphi=(1+\sqrt5)/2,\quad\psi=-1/\varphi,\quad s_0=\sqrt{d_0},\quad z=\log s_0,\quad\ell=\log L,
\quad D_{crit}=L^{2/\varphi^2},\quad G=\varphi^2z-\ell.$$

| 行 | 原参数条件 | 全未来制度 | 有限表示结果 |
|---|---|---|---|
| 1 | $L<1$，任意 $H$ | $\Omega=\Theta(\epsilon)$ | 任意正 $E$，付费精度及证书下可解 |
| 2 | $L=1,H<1$ | 同上 | 同上 |
| 3 | $L=1,H\ge1$ | 单位平台 | 有统一位上限时恰为 $E>1/2$ 可解 |
| 4 | $L>1,d_0<D_{crit},H<1$ | 线性 | 同行1 |
| 5 | $L>1,d_0<D_{crit},H=1$ | 单位平台，包含 $d_0>1$ | 同行3 |
| 6 | $L>1,d_0<D_{crit},H>1$ | 任意 $\epsilon>0$，$\Omega=\infty$ | 任意有限逐源字亦不能保证有限统一 $E$ |
| 7 | $L>1,d_0=D_{crit},H\le1$ | 全零未来 | 有效付费制度证书下准确零输出 |
| 8 | $L>1,d_0=D_{crit},H>1$ | 无限放大 | 同行6 |
| 9 | $L>1,d_0>D_{crit},H<H_*$ | 全零未来 | 同行7 |
| 10 | $L>1,d_0>D_{crit},H\ge H_*$ | 无限放大，等号达到 | 同行6 |

准确记录在全部十行都有 $\Omega(0)=0$。平台的原模量保持 $\Omega(\epsilon)=1$ 在充分小的正区间，$\Omega\le2$，$\epsilon\ge2$ 时 $\Omega=2$；不主张中间完整曲线。

这张十行表的全时间制度、实际支撑与达到阈值分别复用本卷定理 24.2、18.2–18.4、19.1–19.3、25.1–28.2；有限表示一栏由下述新条件构造与障碍承担。以下说明保留原判据的完整关系，有限支持只用于数学证书，不授观察者计数。非零标签可能的组成恰为

$$\mathcal S=\{(1,0),(0,1)\}\cup\{(m,n):m,n>0,\ (m,n)\notin(2\mathbb N)^2\}.$$

必要性由单位轴的 $\mathbb F_2^2$ 分次给出，纯标签至少两叶含零 cherry。充分性从 $\langle\beta,\alpha\rangle$ 出发，每次双左接一种叶加2而不消零；奇/奇全部可得，一次左接补偶/奇或奇/偶。根反序给相反符号。每个见证仍是一棵真实有限有序树。

原叶界允许的 $(r,s)$ 恰为 $s_0\le s\le L^2,s/L\le r\le L$。必要性由 $s\le|a||b|\le Lr$；充分性取正交 $a=(s/r)e_1,b=re_2$。正交化保持 $B,\Delta$ 和两个尾范数，且由第50节投影恒等式把 $q_0$ 降到最小值 $(s/r)^mr^n$；随后同比缩叶降到 $s=s_0$，每个树值按其真实叶数缩小。故非零三读可行当且仅当某个 $\mathcal S$ 中组成及 $v\in I=[z-\ell,\ell]$ 满足

$$f_0=mz+(n-m)v\le\log H,\quad f_1=nz+mv\le\log H,\quad f_2=f_0+f_1\le\log H.$$

正交准备和该组成的真实树反向实现三项。非零未来的增长量为 $\Gamma=\log r+\varphi\log s$。取 $l_i=\log q_i$，递推的准确解是 $\log q_j=F_{j-2}l_1+F_{j-1}l_2$。两根 $\varphi,\psi$ 的初值验证给 $F_n=(\varphi^n-\psi^n)/\sqrt5$，从而

$$\log q_j=\frac{\varphi^{j-2}}{\sqrt5}(l_1+\varphi l_2)-\frac{\psi^{j-2}}{\sqrt5}(l_1+\psi l_2),\qquad l_1+\varphi l_2=(m+\varphi n)\Gamma.$$

正权重和 $|\psi|<1$ 证明趋零、趋1、趋无穷分别对应 $\Gamma<0,=0,>0$。

若 $G<0$，三读最小上界的下确界为0且不达到。$z>0$ 时令 $\eta=\ell/z-1>\varphi$，选互素正整数比 $1+1/\eta<n/m<\eta$，取任意大奇数倍，$v=z-\ell$ 使 $f_0,f_1,f_2$ 都趋负无穷。$s_0\le1$ 的情形可取 $s$ 严格在 $s_0$ 与 $\min(1,L^2)$ 之间及 $r=s/L$，这使 $\Gamma<0$；其标准替换轨道的尾范数趋零，有限平移后全部三读小于任意 $H$。$s_0=1,L>1$ 时改取 $1<s<L^{1/\varphi^2}$，同样 $\Gamma<0$。非零有限树在 $\Delta>0$ 下范数正，故下确界不达到。

若 $G=0$，$z>0,\eta=\varphi$，端点三项为 $-\varphi e,e,-e/\varphi$，$e=n-\varphi m\ne0$。它们最大值严格正。连续 Fibonacci 组成给 $e\to0$，且不双偶，故读界下确界1而不达到。正权重式和 $\Gamma\ge G$ 也排除 $H\le1$ 的非零来源。

若 $G>0$，定义

$$\log H_* =\min_{(m,n)\in\mathcal S}\min_{v\in I}\max(f_0,f_1,f_2).$$

叶 $\alpha$ 的等叶长 $\sqrt{s_0}<L$ 给上界 $s_0$。并且 $f_1+\varphi f_2=(m+\varphi n)(v+\varphi z)\ge(m+\varphi n)G$；若三个 $f_i\le z$，则 $(m+\varphi n)G\le\varphi^2z$。所以只需有限支持 $m+\varphi n\le\varphi^2z/G$，其它组成不能持平或改善该叶上界。每个闭区间内三仿射线最大值在端点或线交点达到最小；有限最小严格正，故 $1<H_*\le s_0$ 且由真实树和正交准备达到。两种更宽截止只要保留完整三线测试，亦给同一个阈值，不增加源大小限制。

特别地，若有限有理证书给 $L_+>1,d_-\ge L_+,H_+>0,H_+^2<d_-$，并且供方确证真实叶界、行列式下界和三读界分别不超过/不低于这些数，则未来全零。证明：$z=\log\sqrt{d_-},\ell=\log L_+$ 有 $2z\ge\ell>0$。每个混合支持 $(m,n)$ 在 $v\ge z-\ell$ 处满足 $f_2\ge mz+n(2z-\ell)\ge z$；叶 $\beta$ 的 $f_1=z$；叶 $\alpha$ 在 $v\ge0$ 时 $f_2\ge z$，在 $v<0$ 时 $f_0>z$。故非零三读最大至少 $\sqrt{d_-}>H_+$，矛盾。等叶长的 $\alpha$ 又达到 $\sqrt{d_-}$（当类非空且 $d_-<L_+^4$），与原阈值一致。这只是一个充分有限证书，不能穷尽分类所有任意实数临界条件。准确零解码仍先支付原三读两更新；零类证书既可公开按制度给出，也可属于计费的来源承诺。

线性行由第52节有条件线性界，准确实际对亦可直接套用其中一个作报告，给 $\Omega\le K\epsilon$。每行存在上述严格允许的非零来源，绕垂直于非零 $x_3$ 的轴作小正向旋转同时转两叶，记录距离至多 $H|\theta|$，$x_3$ 距离为 $2q_3\sin(|\theta|/2)$，给线性下界。旋转保持 Gram、叶界和全部读界。零行由不存在非零标签来源、退化尾零而准确成立。平台和增长的完整实际见证在后两节给出。

原小平台上界也保留：令实际三读距离 $\epsilon$，$H$ 的有效读上界取1。相同符号/零分支 $|x_3-x'_3|\le2\epsilon$；异号时两个归一化三重积相差至少 $2c$。归一化向量差至多 $2\epsilon/q_i$，三重积逐因子相减给 $2c\le2\epsilon(q_0^{-1}+q_1^{-1}+q_2^{-1})\le6\epsilon/q_2$，其中 $q_0,q_1\ge q_2$ 由投影幅度关系得到。所以 $q_2\le3\epsilon/c$，锚差 $\le|w-w'|+2|w|\le(2+6/c)\epsilon$。同相位单位方向与幅度均不超过1：任意范数不超过1的向量 $v,v'$ 的缩小倍数 $sv,s'v'$（$s,s'\in[0,1]$）距离不超过 $\max\{|v|,|v'|,|v-v'|\}$，因为距离是两倍数的凸函数，矩形顶点给该上界。对相位锚 $x_1,x_2,x_3$，$\epsilon\le(2+6/c)^{-1}$ 时锚间距离均不超过1，故全未来距离不超过1。全时上界2由幅度界；相反单位/近单位相位及收缩对给小误差下界1（第55节），根反序或转到反向的真实单位极限给 $\epsilon\ge2$ 时下界2。这些是数学原制度，不能作为任意实数制度分类的执行器。

## 54. 单位读界下的有限平台库及更紧点态界

**定理 54.1。** 对所有准备，只要 $q_0,q_1,q_2\le1$，无行列式下界，供应任意有理 $\tau>0$ 就能以有限报告给统一误差 $E=1/2+\tau$。令首个未来周期锚

$$A_3=x_3,\quad A_4=q_2^2x_1,\quad A_5=q_1^2q_2^2x_2.$$

把 $A_3/2,A_4/2,A_5/2$ 分别用于相位 $0,1,2$。每个后续同相位向量是对应 $A_r$ 的 $[0,1]$ 倍数，因此理想误差至多 $|A_r|/2\le1/2$。用报告替换为 $Z/2,V_yy_1/2,U_yV_yy_2/2$，是次数2、3、5的库。

证明。$q_1,q_2\le1$ 使指数非负增加时不增幅度，故所有 $q_j\le q_3=q_1q_2\le1$，三条射线固定；各相位从 $j=3,4,5$ 开始，之后单项式系数不增。零/依赖分支照样成立。$e\le1$ 时 $|y_i|\le2$、$||y_i|^2-q_i^2|\le3e$。第51节给 $|Z-x_3|\le9\sqrt e$。第二锚差至多 $4e+3e=7e$；第三锚差至多 $16e+12e+3e=31e$。所以全部未来误差至多

$$\frac12+\frac{31}{2}\sqrt e+\xi_{out}.$$

取 $e\le\min(1,(\tau/31)^2)$、$\xi_{out}\le\tau/2$ 即得结论。整个库用相同有限符号算法；不把看似不在像中的报告判成另一来源。

**定理 54.2（幅度加权改进）。** 理想库 $(q_2x_1/2,q_1x_2/2,x_3/2)$ 每个中心长度为 $q_3/2$，全部未来误差至多 $q_3/2$。这比普通半锚 $(x_1/2,x_2/2,x_3/2)$ 的逐相位 $q_i/2$ 界更紧。若有限范数近似误差至多 $\eta$，把报告范数近似裁剪到 $[0,1]$ 得 $u,v$，执行 $(vy_1/2,uy_2/2,Z/2)$，则误差至多

$$q_3/2+\max\{e+\eta/2,(9/2)\sqrt e\}+\xi_{out}.$$

原有条件域还有更紧的 $q_3/2+\max\{e+\eta/2,8e/c_-\}+\xi_{out}$。

证明。每相位 $0\le q_j\le q_3$，到其射线中点的距离至多 $q_3/2$。范数为1-Lipschitz，裁剪对 $q_i\in[0,1]$ 不增加误差，故 $|u-q_1|,|v-q_2|\le e+\eta$。第一中心差 $\le(v e+q_1(e+\eta))/2\le e+\eta/2$，第二相同；第三使用第51节。真实零、极小和符号分支不需要分母。

范数近似是有限整数运算：若向量为 $n_k2^{-b}$，整数 $S=\sum n_k^2$，取 $p\ge b$，令 $t=\lfloor\sqrt{S2^{2(p-b)}}\rfloor$，则 $t2^{-p}\le|y|<(t+1)2^{-p}$。二进制整数平方根由有限区间平方比较搜索取得，包含完全平方数，宽度 $2^{-p}$。这明确支付了 $\eta$，未询问真实实数范数。

一个完整有限预算为 $\eta\le\tau/4,\xi_{out}\le\tau/2$，以及 $e\le\min\{1,\tau/4,(\tau/9)^2\}$；有 $c_-$ 时可把最后平方项改为 $c_-\tau/16$。前两个中心误差不超过 $3\tau/8$，第三中心误差不超过 $\tau/2$，故统一误差至多 $1/2+\tau$。程序用范数分数位数 $\max\{b,\operatorname{precision}(\tau/4)\}$，所以范数求值的整数移位始终合法。

上述加权库和首个未来周期多项式库不互相点态支配。例 $q_1=q_2=1/2$ 时，$j=4$ 的加权中心恰为 $x_4$，多项式半中心误差 $1/16$；该相位足够晚时加权误差趋 $1/8$，多项式半中心误差趋 $1/16$。多项式库的相位最坏界分别是 $q_3/2,q_1q_2^2/2,q_1^2q_2^3/2$，其全相位最大仍为 $q_3/2$。加权库的全相位点态界具有真实量化价值，多项式库则免去范数算术。

**带门控的归一化比较。** 在有 $c_-$ 的原平台域，令 $A_c=\max(1,16/c_-)$，$e\le1/(8A_c)$。若 $|Z|\le1/2$，常零的误差至多 $1/2+A_ce$。否则真实 $q_3>3/8$，$q_1,q_2\ge q_3$，三个真实锚范数至少1/4，报告锚至少1/8。规范化不等式 $|v/|v|-x/|x||\le2|v-x|/|x|$（加减 $v/|x|$ 即得）给方向误差至多 $8A_ce$。报告范数在 $[0,4]$；有理平方比较二分到误差 $\eta_n\le\min(1/16,\nu/16)$，中点分母至少1/16，故除法方向误差至多 $16\eta_n\le\nu$。三半单位方向再舍入给 $1/2+4A_ce+\nu/2+\xi_{out}$。取 $e\le\tau/(16A_c),\nu\le\tau/2,\xi_{out}\le\tau/4$ 可严格小于 $1/2+\tau$。门控零尾确实走零支路。它是有效的有条件线性噪声保证，但域比定理54.1窄，误差系数比定理54.2保守；无需把它另作为主要执行核。普通半锚 $(x_1/2,x_2/2,x_3/2)$ 的全未来理想界是 $\max(q_1,q_2,q_3)/2\le1/2$；以 $(y_1/2,y_2/2,Z/2)$ 替换并舍入，全部准备域有 $1/2+(9/2)\sqrt e+\xi_{out}$，有条件域有 $1/2+8e/c_-+\xi_{out}$。证明是逐相位真中心误差加相应的半锚误差；$e/2\le(9/2)\sqrt e$，且 $c_-\le1$ 时 $e/2\le8e/c_-$。它的噪声常数优于首个未来周期库的保守常数，却没有 $q_3/2$ 的理想点态界。其有限执行说明仅为调用共同 `anchors`、各乘 dyadic $1/2$、舍入并按同一个流解析器选相位；没有归一化、范数口或另一套控制机制。加权库同时保留 $q_3/2$ 与更好的噪声常数，但支付有限范数取得；这三种取舍不能只按常数或次数删掉实际点态信息。

## 55. 两个平台的实际族与有限完整记录端点

**实际族引理。** 下述规范树、叶数索引及缩放族复用本卷定理 27.2 的已发表构造；只取其中较慢的一族并允许第一平台的近单位成员也都严格收缩。 两个平台均有一列实际严格收缩来源，固定每个时刻的向量极限为 $U_j=e_1,e_2,-e_3$ 的三循环，并且三读趋向 $U=(e_1,e_2,-e_3)$。

第一平台取同一树 $\alpha$、$p_\lambda=(\lambda e_1,\lambda e_2)$，$\lambda\uparrow1$ 且 $\lambda^4\ge d_0$。$q_j=\lambda^{F_{j+1}}$，固定 $j$ 趋1，每个 $\lambda<1$ 随 $j\to\infty$ 趋0。第二平台选择

$$\max(1,s_0)<s_*<L^{1/\varphi^2},\quad a_*=s_*^{\varphi^2},\quad r_*=s_*^{-\varphi},
\quad p_*=(a_*e_1,r_*e_2),\quad C_* =\log a_*.$$

两个叶长严格小于 $L$，$\Delta_*=s_*^2>d_0$。规范实际树 $T_k=\rho^k\alpha$ 的叶数为 $F_{k+1}$，$\log|E_{p_*}(T_k)|=C_*\psi^k$；两初值、原有序递推给两式。只取正的12倍数 $k$，令

$$\tau_k=2(1+C_*)\varphi^{-k}/F_{k+1},\qquad s_k=(T_k,e^{-\tau_k}p_*).$$

在相对时刻 $h$ 的对数为 $C_*\psi^{k+h}-\tau_k F_{k+h+1}$。$h=0,1,2$ 时正项不超过 $C_*\varphi^{-k}$，减项至少 $2(1+C_*)\varphi^{-k}$，故三读都严格小于1。$\tau_k\to0$，全部足够晚成员仍有 $\Delta_*e^{-4\tau_k}\ge d_0$ 和叶界。固定 $h$ 时两项趋0，相位由 $k\equiv0\pmod3$ 固定；每成员 $\Gamma=-(1+2\varphi)\tau_k<0$，故整个尾趋零。这里每成员的九个真值来自同一树及同一数值准备，不是可行边缘的乘积。

若 $d_0>1$，此平台甚至没有非零中性成员：$q_1,q_2\le1$ 及 $\Gamma=0$ 会迫使 $q_1=q_2=1$，两幅度对数方程的整数组成行列式 $m^2+mn-n^2\ne0$（否则整数比为黄金无理根），继而 $r=s=1$，与 $\Delta\ge d_0>1$ 矛盾。严格收缩族仍成立。

该族还证明原模量平台下界。给 $\epsilon,\eta>0$，先固定一个三读到 $U$ 小于 $\epsilon/2$ 的真实收缩成员，再固定足够晚的相位1时刻使其幅度小于 $\eta$，最后选族中足够晚的另一成员，使三读到 $U$ 小于 $\epsilon/2$ 且该固定时刻幅度大于 $1-\eta$。两实际来源的 $d_3\le\epsilon$，未来距离至少 $1-2\eta$；令 $\eta\downarrow0$ 得 $\Omega(\epsilon)\ge1$。将一个近单位成员两叶正向旋到该相位的反向，所有三读距离仍至多2，未来距离趋2，给 $\Omega(\epsilon)=2$ 对 $\epsilon\ge2$ 的下界。限次序已经指定。

**定理 55.1。** 在每个平台，任意源感知编码器的完整记录若有统一有限位上限，则不可能统一保证 $E\le1/2$，即使三个读数本身无噪且允许编码器知道整个来源。每个 $E>1/2$ 则在充分细的付费精度下由定理54.1实现。

证明。将上述整个族同时旋转两叶，使未来相位 $j\equiv1\pmod3$ 的单位极限为任意单位方向 $u$。正向旋转保持所有约束。有限记录字母表为 $\mathcal A$。对每个 $u$，无限族中有一个记录字在无穷子列重复，选其中之一 $a(u)$。不同的至少两个方向 $u\ne v$ 具有同一 $a$。对每个固定 $j\equiv1\pmod3$，沿各自重复子列的固定时刻极限，解码值 $r_a(j)$ 必须同时满足 $|r_a(j)-u|,|r_a(j)-v|\le E$。从其中一个重复子列固定一位真实收缩成员，随后让 $j$ 在该相位趋无穷，得 $\limsup|r_a(j)|\le E$。有界子列极限 $z$ 因而满足 $|z|,|z-u|,|z-v|\le E$。$E<1/2$ 与 $|u|=1$ 的三角不等式矛盾；$E=1/2$ 的等号迫使 $z=u/2=v/2$，仍矛盾。限次序不互换，也不要求源中存在中性成员。源相关代码、选择数据若另存于“程序”也属于 $a$。可数无限字母表不受这里的有限鸽巢证明排除。

## 56. 正噪声三点纤维和特定 dyadic 单元下界

风险的精确定义如下：来源集为所声明的实际类 $\mathcal S_{act}$，报告空间为 $(\mathbb R^3)^3$，兼容纤维为 $\mathcal A_\delta(y)=\{s:\max_{i\le2}|y_i-x_i(s)|\le\delta\}$。允许的估计器 $D(y,j)$ 是所有集合函数，不假定可计算或有限记录；定义

$$R_\delta=\inf_D\sup_{s\in\mathcal S_{act}}\ \sup_{y:\ s\in\mathcal A_\delta(y)}\ \sup_{j\ge3}|D(y,j)-x_j(s)|.$$

有限记录定理则单独量化有限字编码 $a(s)$ 及固定 $D(a,j)$，不能把这个实数报告界面的 $\delta=0$ 值直接搬到有限字界面。

**定理 56.1。** 令 $R_\delta$ 为原三次读完整乘积误差球上、所有集合函数序列估计器的最坏风险。在两个平台的每一个中，对每个 $\delta>0$，选择 $0<\theta<\pi/4$ 使 $2\sin(\theta/2)<\delta/2$，就有

$$R_\delta\ge \frac1{2\cos\theta}>\frac12.$$

证明。取共同完整报告 $U=(e_1,e_2,-e_3)$，以 $Q_\pm$ 表示绕 $e_3$ 的正向 $\pm\theta$ 旋转。把第55节的族两叶同时旋转，保留同一字面树。所有足够晚的成员之三读到 $Q_\pm U$ 的距离小于剩余 $\delta/2$，故都兼容同一个 $U$。再固定一个足够晚的未旋转实际收缩成员，它也在该完整纤维中。旋转竞争者每次执行内的准备始终固定；两竞争世界的准备可不同，这是原来源量词允许的比较，不是声称其数值叶对相同。

固定 $j\equiv0\pmod3$，先让族索引趋无穷，两个真实未来趋于 $u_\pm=(\cos\theta,\pm\sin\theta,0)$。若一个估计器有有限风险 $r$，其在数据 $U$ 上的输出 $r_j$ 满足 $|r_j-u_\pm|\le r$。然后保持已固定的未旋转收缩成员，让这个相位的 $j\to\infty$，得到 $|r_j|\le r+o(1)$。取有界子列极限，$\{0,u_+,u_-\}$ 被半径 $r$ 的球包围。

其最小包围球半径恰为 $r_\theta=1/(2\cos\theta)$。投影去掉第三坐标、对第二坐标反射后取中心平均，凸性不增最大距离，故可取中心 $te_1,t\ge0$。目标为 $\max\{t,\sqrt{1+t^2-2t\cos\theta}\}$。两项相等的点为 $t=r_\theta<\cos\theta$；$t\le r_\theta$ 时第二项至少 $r_\theta$，$t\ge r_\theta$ 时第一项至少它，且该点达到。于是每个估计器 $r\ge r_\theta$，再取下确界。证明对没有中性实际成员的 $d_0>1$ 也完全成立。原规范树的 $x_3=e_1$，所以本证明使用相位0；绕 $e_3$ 的旋转固定的是相位2的 $-e_3$。

**定理 56.2（仅针对最近格点仪器）。** 若仪器合同是对真实精确坐标作最近步长 $h=2^{-b}$ 的格点舍入，则在任意有限 $b\ge0$，且记录仅含九个舍入坐标、公共 $b$ 及同一日程／动作／Stop 元数据，没有另附源相关建议、程序选择或精确身份侧信道，则该记录解码器必须有

$$E=1/2+\tau\quad\Longrightarrow\quad\tau\ge 2^{-2b}/384.$$

证明。取 $\theta=h/8\le1/8$。$U$ 在格点上，每个旋转单位坐标与 $U$ 差至多 $\theta\le h/8$；取族充分晚，使附加真坐标差严格小于 $h/8$，并固定同样足够晚的未旋转收缩成员。所有坐标均在 $U$ 的单元内部，距离小于 $h/4<h/2$，因此九个报告字严格相同，任何平局规则都无关。按上一定理两次极限，风险至少 $r_\theta$。对 $0\le\theta\le1/8$，交错 Taylor 余项给 $\cos\theta\le1-\theta^2/2+\theta^4/24\le1-\theta^2/3$。故

$$r_\theta-1/2=(1-\cos\theta)/(2\cos\theta)\ge\theta^2/6=h^2/384.$$

得到 $b\ge\frac12\log_2(1/(384\tau))$ 在右边为正时的必要条件。定理54.1给固定参数下 $b=O(1+\log(1/\tau))$ 的充分阶（需相应小的传感误差）；不声称常数最优。单元论证不适用于任意编码器，也不能未经校核应用到“先有限近似再舍入”的另一个仪器。后者的原理见第59节。一般任意有统一位上限的编码器只有第55节的端点结论。

对完整误差球还复用一般纤维不等式 $\Omega(2\delta)/2\le R_\delta\le\Omega(2\delta)$，但其上界是抽象选择而非有限算法。证明：任一对三读距离不超过 $2\delta$ 的实际源兼容共同中点数据，三角不等式迫使任意统一估计器的误差至少为其未来距离一半；取上确界得左界。对每个非空兼容纤维选择其中一实际源，把该源未来作为输出；纤维内每两源三读距离不超过 $2\delta$，故风险不超过右界，空纤维任意定义即可。此选择不供应付费的可执行来源取得。下述三个线性行用定理52.1的有条件直接公式替代选择，结合第53节的旋转下界，得到 $R_\delta=\Theta(\delta)$ 当 $\delta\downarrow0$；两个零行常零给全部噪声下风险0。因此任何固定正完整传感误差球在非零线性类中都有正风险地板，不能从同一旧记录要求任意准确。

**风险不连续。** $R_0=0$ 因第50节准确三读公式。定理54.1的理想报告算术给 $R_\delta\le1/2+(31/2)\sqrt\delta$，$\delta\le1$；有条件的加权或门控界还给线性趋近。与定理56.1合起来，$\lim_{\delta\downarrow0}R_\delta=1/2$，但每个正 $\delta$ 都严格大于1/2。$R$ 的定义允许任意实数数据和所有集合函数，故 $R_0=0$ 不等价于统一有限位记录的端点可达。变量有限字、固定上限字、任意实记录与无限细化名字都要分别声明。原来的 $\delta\ge1$ 平台风险恰1也保留：常零上界1，反向单位/近单位方向在共同零报告中逼近距离2，给下界1。这里没有完整有限正噪声曲线或最优常数。

## 57. 三个增长制度中的任意有限字障碍

**定理 57.1。** 在表中行6、8、10，包括达到的 $H=H_*$，任何每源有限的二进制完整记录编码器，都不能在原全部实准备上保证任何有限统一全未来误差 $E$。记录长度可以依源任意大；源相关程序、元数据与建议也必须包含在有限字中。

证明。首先每行有实际非零增长来源。$G\le0,H>1$ 时，选择 $1<s_*\le L^{1/\varphi^2}$ 且 $s_*^2\ge d_0$，临界正交 $p_*=(s_*^{\varphi^2}e_1,s_*^{-\varphi}e_2)$ 的规范树 $T_k$ 在足够晚时三读接近1，严格小于 $H$。$G=0$ 允许第一叶恰为 $L$；作小的 $r\mapsto re^v,a\mapsto ae^{-v}$，$v>0$，保持 $s,\Delta$，叶长仍满足界（第二叶原有严格余量），有限三读由连续性仍小于 $H$，$\Gamma=v>0$。$G<0$ 可先选严格临界余量，完全相同。$G>0,H\ge H_*$ 时用第53节的实际达到者，$\Gamma\ge G>0$，不需移开任何等号。

固定此一真实树及准备，绕非零 $x_1$ 的轴以一个长度小于 $\pi$ 的实角区间旋转两叶。各成员树相同，全部范数和 Gram 相同，故保留每个活跃界。相位2的 $x_j$ 垂直于此轴；任意不同角 $\theta,\theta'$ 有

$$|Q_\theta x_j-Q_{\theta'}x_j|=2\sin(|\theta-\theta'|/2)q_j\longrightarrow\infty\qquad(j\equiv2\pmod3).$$

因此得到不可数个两两无限分离的实际同树历史。有限二进制字只有可数多个；两个不同角必须取得相同完整字。共同解码序列若在两端误差均不超过有限 $E$，逐时刻三角不等式会给距离至多 $2E$，矛盾。该证明比固定有限字母表下界强，且不能用一个不收费的源相关程序绕过。

同样可以把角区间取得任意小，使整段旋转的三读均兼容一个正误差球数据；其中未来距离无穷，故原完整误差球 $R_\delta=\infty$ 对每个 $\delta>0$。准确任意实记录的 $R_0=0$ 则依旧成立。增长源中也有零标签树；有证书的全零类必须单独处理，不能把一个有限精度报告的“看似零”当作准确实数相等分类。

**已发表的达到例。** 以下阈值和八叶实际树复用本卷定理 31.1 的覆盖证明及准确求值。 $L=6,d_0=4$ 的实际阈值 $H_*=32/27$。有限覆盖来自 $559^2<5\cdot250^2$ 及 $2^{103411}>6^{40000}$，它们给 $\varphi^2\log2-\log6>\varphi^2\log2/80$，故任何能改善叶上界2的支持组成有 $m+n<80$。$m>n$ 时三线最优最大对数 $(m+n-n^2/m)\log2>m\log2$，不能改善2；$n\ge m$ 时所有斜率非负，端点准备 $(6e_1,e_2/3)$ 给幅度 $6^m/3^n,2^n/3^m$ 及其乘积。两个纯叶的最优读界都是2；准确测试 $m+n\le80$ 的2380个混合非双偶组成得到唯一最优 $(3,5)$ 和 $32/27$。该有限检验的完整整数／Fraction 代码及输出在第63节列出，覆盖证明已经给出。

实际树从 $k=\langle\beta,\alpha\rangle$ 双左接 $\alpha$ 一次、双左接 $\beta$ 两次，组成 $(3,5)$，单位标签 $-f_3$。字面求值得 $x_0=(0,0,8/9),x_1=(-32/27,0,0),x_2=(0,-256/243,0),x_3=(0,0,8192/6561)$。三个取得范数最大恰为 $32/27$，而 $\Gamma>0$，所以阈值等号本身受定理57.1约束。

## 58. 三项非冗余的条件例外

**逐实例收缩证书。** 在读界1的平台中，另行供应并付费验证 $q_1q_2\le\kappa<1$ 的有理证书，则对任意 $E>0$ 有有限头/尾方法，但费用依 $\kappa$。因为 $a_j\le b_j$，

$$q_j=(q_1q_2)^{F_{j-2}}q_2^{F_{j-1}-F_{j-2}}\le\kappa^{F_{j-2}}.$$

取 $T$ 使 $\kappa^T\le E/2$，最小 $J\ge3$ 使 $F_{J-2}\ge T$，整个 $j\ge J$ 输出零。有限头中报告范数至多2、第三锚误差至多 $9\sqrt e$，$N=F_J$，乘积替换与第52节相同，保守给 $|P_j-x_j|\le B\sqrt e$，$B=2^{N+1}(9+N)$。取 $e\le\min(1,(E/(2B))^2)$ 和输出误差 $E/2$。一切搜索、幂和截尾有限，同一执行核实现。若已有 $c_-$，同一多项式核可改取 $B_c=2^{N+1}(\max(1,C_c)+N)$，用 $e\le\min(1,E/(2B_c))$ 取得线性预算；带范数近似的旧三锚形式另给有限头 $(\max(1,C_c)+D)e+D\eta+\xi_{out}$，$D=F_{J-1}$，因为系数因子在 $[0,1]$ 时逐因子替换至多 $D(e+\eta)$。本方法不需要后续源读取；同一次已取得精度可否认证 $\kappa$，由范数上包络 $|y_i|+e$ 的乘积是否严格小于1决定，固定噪声地板可能使认证失败。不能安装停止后免费细化口。没有一致 $\kappa$ 就没有本段一致成本，第55节已给障碍。

**精确有限有理回复的受限表示类。** 若仪器真正承诺原三次准确回复都是给定有限有理数，零传感误差、没有量化偏差，则所有实际准备包括退化零分支，对每个有限 $j$ 都可准确求未来。把九个有理数化成一个正共同分母 $D$，以整数向量替换 dyadic 的分子/分母对：加法、乘法、叉积、点积和正分母下的符号均准确，多项式核给分母 $D^{F_j}$。若输入分子和共同分母总位宽受 $B$ 控制，分子位宽为 $O(F_j(B+1))$，分母位宽 $F_j\log_2D+O(1)$，约分不会增大。dyadic 情形 $D=2^b$ 的可用分母指数为 $bF_j$；若真读界为 $H$，分子位宽 $O(1+F_j[b+\log_2(1+H)])$，指数头宽 $O(j+\log(b+1))$。这是无界整数机器上的逐请求终止定理，不是固定有限状态全源机器，也不保证任意实数来源能发出这些准确有限字。逐次带符号叉积是相同准确结论的另一实现，不必并存两套核。

**另供可细化 Cauchy 名字。** 若另行供应原三次准确向量的可复用认证 dyadic 名字，允许请求任何有限精度，此为无限信息表示扩展。它使每个有限 $(j,E)$ 可以计算，即使增长。先取得粗近似及误差界，用其坐标绝对值和加1构造有限有理 $\bar H\ge1$ 包住真三读。令 $R=\bar H+1,N=F_j,B_j=R^{N+1}(C_s+N)$。取名字精度使 $e\le\min(1,(E/(2B_j))^2)$，执行同一核并用输出误差 $E/2$。标量乘积次数至多 $N$，真/报范数至多 $R$，真第三锚至多 $R^2$，逐项替换给 $|P_j-x_j|\le B_j\sqrt e$，所以有限终止。若有 $c_-$ 可改线性精度。本扩展的名字读取及供应成本另计，不能把每个请求只读有限前缀解释成一个固定有限完整记录；原接口在 Stop 后没有这个精度请求权。附带 `named_query` 先付费访问精度0的三个名字，其同时误差至多1，以各行整数坐标绝对值之和加1生成 $\bar H$；然后 `setup_name_query` 用上述公式选择精度，再付费访问一次名字。`read_name(b)` 的明确合同是返回九整数表示的三向量并认证同时误差不超过 $2^{-b}$，访问与供方生成费用另计。它不调用真实来源的新 Read。

**输出宽度的实际下界。** 原树 $\alpha$ 和 $p=(2e_1,2e_2)$ 满足 $L=2,H=4,d_0=1$，其 $q_j=2^{F_{j+1}}$。以通常二进制固定点数值输出、绝对误差 $E<1/2$ 时，一个非零坐标整数部分至少需要 $F_{j+1}+O(1)$ 位；因为该坐标绝对值至少 $2^{F_{j+1}}-1/2$，位长不能缩小。符号和分数精度还要另计。符号幂表达式是另一个收费输出格式，不能用它否定这个位置数值宽度下界。

## 59. 有限生产者、预算及可执行契约

先得到一个付费传感向量 $r_i$，保证 $|r_i-x_i|\le\sigma$。生产者再付费取得每坐标的 $(b+4)$ 分数位有限整数近似 $d_{ik}$，令近似数值为 $d_{ik}2^{-b-4}$ 并保证 $|d_{ik}2^{-b-4}-r_{ik}|\le2^{-b-4}$，随后仅对这个有限整数作最近步长 $2^{-b}$ 的舍入，平局采用预定有限规则。每坐标误差至多 $(9/16)2^{-b}$；向量误差至多 $(9\sqrt3/16)2^{-b}<2^{-b}$，因为 $243<256$。于是总预算

$$e\le\sigma+2^{-b}.$$

给定 $e_*$，选择 $\sigma\le e_*/2$，用有限有理比较选 $b$ 使 $2^{-b}\le e_*/2$。这一生产者没有未知真实坐标的平局判定 oracle。传感近似和守卫位发行都要实际付费；九个守卫字是瞬态资源，不算免费。第56节最近真实格点仪器则是一项不同数学承诺；其单元下界不自动适用本段先近似的生产者。

有限有理证书的一个可执行检查为 $L_+>0,d_->0,0<c_-\le1,c_-^2L_+^4\le d_-$，它推出 $c_-\le\sqrt{d_-}/L_+^2$。附带函数也检查上述充分零证书的纯有理不等式；这些有限检查为固定次数整数/有理算术，保守耗时 $O(C_{pub}^3)$、工作 $O(C_{pub})$。检查不证明现实中的 $|a|,|b|\le L_+$ 或 $\Delta\ge d_-$；这种真值仍须由已付费供方承诺或证据承担。稳定配置的 $\rho<1$ 可来自 $L_+<1$ 或真实读界 $H_+<1$，也可直接是实际 $q_1,q_2$ 的有效上界；`setup_stable` 检查有限数的关系，不能从九个近似字免费推知隐藏真实范围。

第62节完整给出整数参考程序；第63节给出可直接运行的准确核验。dyadic 用 $(n,b)$ 表示 $n2^{-b}$，不要求约分；加法对齐分母指数，乘法相加，符号只比较整数。平方范数和叉积均准确。幂用二进制平方/乘法，$0^0=1$。输出最近舍入的每坐标误差至多 $2^{-p-1}$，故向量误差小于 $2^{-p}$；选择 $p$ 使 $2^{-p}$ 不超过指定 $\xi_{out}$。这把传感、量化、第三锚及系数计算、确实使用的范数包络和最终输出分别置于同一个预算。主稳定核和主平台库的中间算术准确，故中间舍入误差为零；加权库才用第54节的有限范数包络。程序从来不要求报告本身正交或可实现。

请求接口是一枚以流结束标记终止的规范二进制 token，无前导零，必须表示 $j\ge3$；非法 token 由参考程序抛出 `ValueError`：非二进制字符或前导零使用 `invalid binary query`，空 token 或数值小于3使用 `future query must be at least 3`；查询函数不捕获该异常或将其序列化为错误字，准确输出合同只量化合法请求。程序逐字检查，维护 $\min(j,J)$ 和模3，禁止预先把任意长请求读为一个无限宽整数。对于有限头，饱和值等于真实 $j$；饱和值为 $J$ 时整个尾输出零。平台只需饱和值3和模3。所有字符都读取，包括已饱和后的字符，故合法性与查询长度成本明确。

## 60. 同一程序的位、时间、工作及源侧费用

记 $C_{pub}$ 为实际保留的公共有理数、证书、格式、程序选择与可变参数总位宽，$M_{id}$ 为实际来源/坐标系/时刻/动作/Stop 元数据宽度。若 $e\le1,q_0,q_1,q_2\le\bar H$，报告分子每个可用 $B=O(1+b+\log_2(1+\bar H))$ 位。原完整报告是九个这样的字，故 $9B$，再加公共 $b$、格式和 $M_{id}$。记实际完整程序、解释器及整数/有理算术库的保留位数为 $C_{prog}$，它们是有限而有价的。主稳定配置的保留位数为 $9B+C_{pub}+M_{id}+C_{prog}+O(\log(b+1)+\log(J+1)+\log(p+1))$；这里 $C_{pub}$ 包含配置中实际保留的 $R,K,e_*$ 等有理数，并非只计原始参数。参考程序每请求重算第三锚，不隐藏缓存；缓存若另选则还支付其三字。平台实现另保留九个舍入后的库坐标，各 $p+O(1)$ 位；本配置保留原报告时同时计 $9B+9(p+O(1))$。所有配置保留程序和证书，不能把设计文稿大小当成观察者内存。

零制度配置的 `zero_query` 只须保留有效制度／来源证书、公共程序和合法日程／动作／Stop 元数据，按其实际位宽 $C_{pub}+C_{prog}+M_{id}$ 收费；若还保留九个报告，另加 $9B$ 和格式位。原三读两更新及报告的瞬态取得仍须支付。规范请求的解析时间为 $O(\lambda_q)$、工作状态为 $O(1)$，不缓存任意长请求；三个零坐标及固定指数头的输出为 $O(1)$ 位。

稳定设置中 $T=O(1+\log_+(1/E)/(1-R))$，$J=O(1+\log(T+1))$。若 $J>3$，最小性给 $F_J<2T$；$T=0$ 或 $J=3$ 则整个头为空。以 $N=\max(2,F_J)$，一个安全工作位上界为

$$W=O(N(B+C_{pub}+1)+p+J+\log(N+1)).$$

一切 dyadic 乘积的指数和分子长度至多次数的常数倍；平方/乘法在程序中不会产生高于最终幂次数常数倍的额外字。固定个数的 $W$ 位字、$O(J)$ 位 Fibonacci/幂指数和 $O(\log(J+1))$ 位流解析状态足够。常规整数乘法、长除法各 $O(W^2)$；二进制整数平方根可用 $O(W^3)$ 的保守平方比较界。程序只在设置中用 Fraction，若对其 Euclid 约分采用保守 $O(W^3)$，搜索 $T$ 的上界可取 $O((T+1)((T+1)(C_{pub}+1))^3)$，工作 $O((T+1)(C_{pub}+1))$；$J$ 搜索用整数加法，$O(J^2)$ 位工作时间上界。输出精度搜索有 $O((p+1)(p+C_{pub}+1)^3)$ 保守上界。它们是一次设置费用，不能只报告后来查询很快。

稳定每请求在长度 $\lambda_q$ 的流上用 $O(\lambda_q\log(J+1))$ 位时间、$O(\log(J+1))$ 解析工作；头部 Fibonacci 逐加计算 $O(J^2)$，两个二进制幂 $O(\log(N+1)W^2)$，叉点积固定次乘加、输出舍入和发射亦计入 $O(W^2+p)$。故共同上界

$$O(\lambda_q\log(J+1)+J^2+\log(N+1)W^2+p),\qquad O(W+\log(J+1))\text{ 工作位}.$$

对固定证书、容差和 $J$，$\log(J+1)$ 是固定常数，所以可说请求解析 $O(\lambda_q)$；这不是参数统一的同一界。平台库设置的次数最多5，工作 $O(B+C_{pub}+p)$，可保守用立方位时间包含有理设置；后来请求 $O(\lambda_q+p)$、解析状态固定有限，库和输出缓冲分开收费。加权库的范数包络另支付所用精度与整数平方根费用；门控归一化另支付有理二分/除法字，不能挪到多项式核上当免费。

逐实例方法费用依其自己的 $J,N$，并非平台统一价格。附带 `setup_instance` 在 $J$ 搜索中每次重算 Fibonacci，故这部分是 $O(J^3)$ 位时间而非稳定设置的 $O(J^2)$；另有 $O(\log(N+1)(N+C_{pub}+1)^3)$ 的保守有理幂/预算费用、按 $\kappa$ 的 $T$ 次有理乘法，以及实际输入/输出精度搜索费用。其后来查询直接调用同一个 `stable_query`，按本段 $J,N,W$ 上界计价。精确有理/名字扩展需随 $j$ 增长的 $O(F_j(B+1))$ 位字，准确或定精度输出另付位长；名字取得成本不由下游乘法定价。精确有理表示的 `parse_unbounded` 则实际构造 $j$，规范请求长度 $\lambda_q$ 下耗时 $O(\lambda_q^2)$、存储 $O(\lambda_q)$ 位，不能套用饱和解析的常空间结论。令该请求的 $W_j=O(F_j(B+1)+j)$，`rational_kernel` 的两个 Fibonacci 逐加循环为 $O(j^2)$ 位时间，两个有理幂最多 $O(j)$ 次乘法；采用含约分的保守立方算术界，完整上界为 $O(\lambda_q^2+j^2+jW_j^3+\lambda_{out})$、工作 $O(W_j+\lambda_q)$ 位，其中 $\lambda_{out}$ 是实际序列化输出长度。dyadic 核可用平方算术界代替立方界。名字扩展还支付精度请求、名字访问、取得字长及其供方计算费用；其下游工作字长把该请求所需精度计入 $B$。`setup_name_query` 的预算幂还计 $O(\log(N+1)[N(C_{pub}+1)]^3)$ 保守位时间和 $O(N(C_{pub}+1))$ 工作位，精度搜索按所选名字位数另计；$N=F_j$，不声称固定有限状态价格。

固定有限精度、固定证书和容差时，上述稳定和平台配置可以实现为有限状态控制器，算术字长和饱和解析均有固定界；变化这些参数是有限控制器族，准确增长求值则是无界算术机。有限状态存在不供应免费指数转移表。

源侧仍有实际准备、共同参考系、物理传感、准确更新、精度发行/核验和隐藏树维护成本。若另供字面树码，实际初叶数 $N_0=m+n$ 时三个已读版本叶数恰为 $m+n,m+2n,2m+3n$，逐节点求三读需要 $4m+6n-3\le6N_0-3$ 次叉积，节点和深度工作按实际表示收费；该精化以实际叶组成递推证明，但没有把计数或代码读口加入原协议。若实际实现字面两次替换，扫描及发出节点需 $O(N_0+N_1+N_2)$ 次节点动作，$N_1=m+2n,N_2=2m+3n$；节点字段、深度栈和每次内部叉积的算术精度/位成本另计，上述叉积次数不是实寄存器的有限位时间结论。无界树的 Read 不能因下游九个字而被定为固定免费成本。公开数学证书与物理发放/准确性验证是两个责任，不主张任何秒数、能量或物理互恢复。

## 61. 复用的实际球面位下界及证据边界

在每个非零线性域，固定一个第53节实现的允许非零来源，其 $|x_3|=r_0>0$。旋转两叶使该目标遍历半径 $r_0$ 球面，树不变、所有约束保持。球面上取 $(x,y,\sqrt{r_0^2-x^2-y^2})$，$x,y\in[-r_0/4,r_0/4]$，以步长 $3E$ 排网格。不同点 欧氏 距离至少 $3E>2E$，数量为 $\Omega((r_0/E)^2)$。任何统一误差 $E$ 的有限完整记录必须逐点不同，故总位上限至少 $2\log_2(r_0/E)-O(1)$。这是通用球面打包方法接到真实来源映射后的复用，不是唯一的新结果，也不是所有资源的最优下界。它与增长中的不可数字障碍及平台端点/单元下界各有不同量词。

固定稳定证书、固定有界元数据及足够小的目标 $E=2^{-k}$ 时，平方根预算取 $e=\Theta(E^2)$、线性预算取 $e=\Theta(E)$ 都只要求 $b=O(1+k)$，九个报告坐标共 $O(1+k)$ 位；目标的实际有限表示和公共常数也另计。结合上述真实球面下界，源相关完整记录的最优位数阶为 $\Theta(1+\log(1/E))$，不声称最优系数、工作位或时间。任意冗长参数/身份编码的实际长度不能被该渐近式隐藏；固定传感误差地板亦可能阻止这样的更细取得。

此外，在每个非零制度中，任意逐源有限字也不能准确恢复全部实来源：上面固定非零来源的旋转目标构成不可数球面，一个有限字在请求 $j=3$ 只能给一个值，可数全部有限字不可能覆盖该球面。这是 $E=0$ 的一般信息障碍；它不排除稳定域每个固定正 $E$ 的有限解码器族，也不替代平台和增长的更强结论。零行仍须使用另付费有效制度证书，协议照常执行原三读两更新，再准确常零输出。

原始依据是本卷第1–32节的已发表普通定义及证明、原自由树／组成／方向源；第33–47节涉及另外的独立参考取得问题，第48节给出实际成对灵敏度及其声明载体的比较；这些已发表增补不作为这里有限表示设计的前提。下面列出精确复用与未作实例化的形式接口。

| 61来源 | 对应与适用范围 |
|---|---|
| 本卷定义1.1–1.3、定理3.1 | 非空有序树、同次共享叶对、原叉积、原 $\rho$ 和唯一当前源；解释换参不执行换制备。 |
| 本卷引理4.2、定理4.3、5.1、引理16.2、推论16.3 | $U,V$ 对应原五符号 $L,N$；复用带符号尾、三次读准确恢复式及实际投影下界，零／依赖分支保留。 |
| 本卷18.1–19.3、24.2–28.2、31.1 | 复用全部组成支撑、三线实际可行性、十行制度、两平台规范收缩族、三个增长行的实际来源以及 $H_*(6,4)=32/27$ 的达到证明。 |
| `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean` | `Source=FreeMagma Bool` 的 true／false 对应 $\alpha$／$\beta$；相同有序节点归纳给语法映射。只复用源对应，不声称有限位恢复已形式化。 |
| `D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric.lean` | 任意状态 $Y$、度量输出 $O$、任意更新 $Y\to Y$ 与读出 $Y\to O$ 及有限 $T\in\mathbb N$；未折扣预测距离是时刻 $0,\ldots,T$ 输出距离的有限最大值，满足伪度量律，零核为有限未来一致。约定32.1已给出 $Y=\mathcal T\times\mathcal P$、更新 $(t,p)\mapsto(\rho t,p)$、读出 $E_p(t)$、$T=2$ 的原树实例；比较初态可限制到 $\mathcal D$，无需该域更新不变。有限结论不要求全局输出距离界；同文件另一个 `bounded_infinite_horizon_prediction_zero_kernel` 才要求整个输出载体的全局距离界。两者均不供应有限位解码或本稿的新 Lean 核验。 |
| `D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk.lean` | 标量 $a^n$、$0<a<1$、有限窗口及正确定全噪声球；只借鉴极限量词，两个平台仍用上述实际树族证明。 |
| `D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius.lean` | 黄金无理转角和 floor 字母读口；仅比较条件，未移植到原向量源。 |

有限线性 Krylov/核定理假设有限维内积载体与线性 $T,C$；它们不是非线性叉积树的有限位实现。秩一 Hankel 全未来风险定理只涉及标量 $a^n$、$0<a<1$、正逐点噪声；它启发极限量词，但不能取代本稿两个实际平台族。机械符号圆周定理假设黄金无理转角和 floor 字母读口，也不是本来源。

主要文献只承担其真实范围：Darpö《Vector product algebras》[原文](https://arxiv.org/pdf/0810.5464v1)初始定义及 Lemma2在特征不为2、交替双线性积、非退化对称型、循环配对和 Gram 范数恒等式下给代数工具，原定向 欧氏 $\mathbb R^3$ 满足它们；本稿的具体公式亦直接证明。Larcombe–Bagdasar《On a result of Bunder involving Horadam sequences: a proof and generalization》[原文](https://www.fq.math.ca/Papers1/51-2/LarcombeBagdasarHoradam.pdf)式(2.2)–(2.3)和完整二阶归纳，在正初幅度、幂参数 $p=q=1$ 下给经典乘法 Fibonacci 工具；实际零、符号、共同准备和来源存在均由本稿处理。Mark Braverman 与 Stephen Cook，*Computing over the Reals: Foundations for Scientific Computing*，[arXiv:cs/0509042v1](https://arxiv.org/pdf/cs/0509042v1)，PDF 第7–9页、§3.1–3.2，以任意可请求精度的 dyadic 名字表示实数，并计入取得及读取近似的时间；这里的名字扩展明确采用这一无限信息合同，而闭合有限记录不取得免费精度口。该文定理1的连续性必要条件不使任意实数符号可计算，也不代替这里的实际纤维下界。本文不依赖未核对的文献断言来证明正结果或下界，不声称全球新颖性或穷尽检索。

本文尚不决定完整有限误差曲线、最佳常数、最优总时间/位数、任意实参数临界分类的有效性、任意真实仪器的有限精度发行或物理价格。这些不是本稿暗设的免费前提。这里新增的是原实际来源上的有限表示／计算构造、平台完整记录端点与严格正噪声纤维、可数有限字增长障碍及明确表示例外；经典身份、通用球面打包及上述已发表来源证明按复用处理。这些普通推导不主张全球新颖性，不给出物理空间、时钟或记忆装置间的互恢复，也没有新的 Lean 核验状态。

## 62. 有限整数参考实现

以下完整代码保存为 `reference.py`，仅使用 Python 整数和标准库 `fractions.Fraction`。代码不调用未知源；配置函数只校验其有限数值关系，传感误差及真实来源证书按第49、59节的供方合同承担。`stable_query` 也承担逐实例截尾配置；`plateau_query` 对多项式库与加权库使用同一相位协议。`rational_kernel` 只用于准确有限有理回复；`named_query` 的回调只属于另供的无限信息名字扩展。返回的三整数和公共分数位数必须按第60节支付保留、缓冲及实际发射位长。

```python
"""Finite-word arithmetic reference. No source calls are made by this module."""
from fractions import Fraction as Q

def isqrt(n):
    assert n >= 0
    if n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length()+1)//2)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid*mid <= n:
            lo = mid
        else:
            hi = mid
    return lo

def add(x, y):
    b = max(x[1], y[1])
    return ((x[0] << (b-x[1])) + (y[0] << (b-y[1])), b)

def neg(x):
    return (-x[0], x[1])

def mul(x, y):
    return (x[0]*y[0], x[1]+y[1])

def power(x, n):
    assert n >= 0
    z = (1, 0)
    while n:
        if n & 1:
            z = mul(z, x)
        n >>= 1
        if n:
            x = mul(x, x)
    return z

def dot(x, y):
    z = (0, 0)
    for a, b in zip(x, y):
        z = add(z, mul(a, b))
    return z

def cross(x, y):
    return tuple(add(mul(x[i], y[j]), neg(mul(x[j], y[i])))
                 for i, j in ((1,2), (2,0), (0,1)))

def scale(c, x):
    return tuple(mul(c, a) for a in x)

def anchors(nums, b):
    assert len(nums) == 9 and b >= 0
    y = tuple(tuple((nums[3*i+k], b) for k in range(3)) for i in range(3))
    w = cross(y[2], y[1])
    d = dot(y[0], w)[0]
    s = (d > 0) - (d < 0)
    return y[1], y[2], scale((s, 0), w)

def fib(n):
    assert n >= 0
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a+b
    return a

def kernel(nums, b, j):
    assert j >= 3
    y1, y2, z = anchors(nums, b)
    u, v = dot(y1,y1), dot(y2,y2)
    a, c = fib(j-2), fib(j-1)
    phase = j % 3
    if phase == 1:
        m, n, anchor = (a-1)//2, c//2, y1
        assert a % 2 == 1 and c % 2 == 0
    elif phase == 2:
        m, n, anchor = a//2, (c-1)//2, y2
        assert a % 2 == 0 and c % 2 == 1
    else:
        m, n, anchor = (a-1)//2, (c-1)//2, z
        assert a % 2 == 1 and c % 2 == 1
    return scale(mul(power(u,m),power(v,n)), anchor)

def round_num(x, p):
    """Nearest p-fractional-bit word; exact ties go away from zero."""
    n, b = x
    if b <= p:
        return n << (p-b)
    d = 1 << (b-p)
    r = (2*abs(n)+d)//(2*d)
    return r if n >= 0 else -r

def round_vec(x, p):
    return tuple(round_num(a,p) for a in x)

def parse(bits, cap):
    """One canonical binary token, ended by iterator exhaustion; no query buffer."""
    assert cap >= 3
    v, phase, seen = 0, 0, False
    for digit in bits:
        if digit not in ('0','1') or (not seen and digit != '1'):
            raise ValueError('invalid binary query')
        seen = True
        d = int(digit)
        v = min(cap, 2*v+d)
        phase = (2*phase+d) % 3
    if not seen or v < 3:
        raise ValueError('future query must be at least 3')
    return v, phase

def output_precision(budget):
    assert budget > 0
    p, h = 0, Q(1)
    while h > budget:
        p, h = p+1, h/2
    return p

def producer_precision(e_star):
    # A paid finite sensor approximation must separately guarantee sigma <= e_star/2.
    return output_precision(e_star/2)

def setup_stable(hbar, rho, E, conditioned_c=None):
    hbar, rho, E = Q(hbar), Q(rho), Q(E)
    assert hbar >= 1 and 0 <= rho < 1 and E > 0
    R = (1+rho)/2
    P = 3*hbar*hbar + 3*hbar + 1
    Cs = 2*hbar+1 + 2*hbar*P
    if conditioned_c is None:
        K = Cs + R/(1-R)**2
        e_star = min(Q(1),(1-rho)/2,(E/(2*K))**2)
    else:
        c = Q(conditioned_c)
        assert 0 < c <= 1
        C = 4*(hbar*hbar+2*hbar+1)/c
        K = C + R/(1-R)**2
        e_star = min(Q(1),(1-rho)/2,E/(2*K))
    T, rpower = 0, Q(1)
    while rpower > E/2:
        T, rpower = T+1, rpower*R
    J, a, c = 3, 1, 2
    while c < T:  # c = F_J
        J, a, c = J+1, c, a+c
    return {'J':J, 'T':T, 'p':output_precision(E/2),
            'b':producer_precision(e_star), 'e_star':e_star, 'K':K, 'R':R}

def stable_query(nums, b, cfg, bits):
    j, _ = parse(bits, cfg['J'])
    if j == cfg['J']:
        return (0,0,0), cfg['p']
    return round_vec(kernel(nums,b,j),cfg['p']), cfg['p']

def setup_plateau(nums, b, tau):
    tau = Q(tau)
    assert tau > 0
    e_star = min(Q(1),(tau/31)**2)
    p = output_precision(tau/2)
    y1, y2, z = anchors(nums,b)
    u, v = dot(y1,y1), dot(y2,y2)
    bank = (scale((1,1),z), scale(mul((1,1),v),y1),
            scale(mul(mul((1,1),u),v),y2))
    return {'words':tuple(round_vec(x,p) for x in bank), 'p':p,
            'e_star':e_star, 'required_b':producer_precision(e_star)}

def plateau_query(cfg, bits):
    _, phase = parse(bits, 3)
    return cfg['words'][phase], cfg['p']

def norm_interval(vector, p):
    """Exact dyadic floor norm and upper enclosure of width 2**(-p)."""
    sq = dot(vector,vector)
    n, b = sq
    assert n >= 0 and 2*p >= b
    t = isqrt(n << (2*p-b))
    return (t,p), (t+1,p)

def setup_weighted(nums, b, norm_p, out_p):
    assert norm_p >= b and out_p >= 0
    y1, y2, z = anchors(nums,b)
    u = norm_interval(y1,norm_p)[0]
    v = norm_interval(y2,norm_p)[0]
    # Floor norms are nonnegative; clipping to 1 is an exact integer comparison.
    u = (min(u[0],1 << norm_p),norm_p)
    v = (min(v[0],1 << norm_p),norm_p)
    bank = (scale((1,1),z), scale(mul((1,1),v),y1),
            scale(mul((1,1),u),y2))
    return {'words':tuple(round_vec(x,out_p) for x in bank),'p':out_p,
            'norm_p':norm_p}

def setup_weighted_budget(nums, b, tau, conditioned_c=None):
    tau = Q(tau)
    assert tau > 0
    if conditioned_c is None:
        e_star = min(Q(1),tau/4,(tau/9)**2)
    else:
        c = Q(conditioned_c)
        assert 0 < c <= 1
        e_star = min(Q(1),tau/4,c*tau/16)
    cfg = setup_weighted(nums,b,max(b,output_precision(tau/4)),
                         output_precision(tau/2))
    cfg.update({'e_star':e_star,'required_b':producer_precision(e_star)})
    return cfg

def verify_conditioned_certificate(L_upper, d_lower, c_lower):
    L,d,c = Q(L_upper),Q(d_lower),Q(c_lower)
    # Arithmetic validation only; physical leaf/Gram promises are supplier owned.
    return L > 0 and d > 0 and 0 < c <= 1 and c*c*L**4 <= d

def verify_zero_certificate(L_upper, d_lower, H_upper):
    L,d,H = Q(L_upper),Q(d_lower),Q(H_upper)
    # Sufficient rational certificate, not an arbitrary-real regime classifier.
    return L > 1 and d >= L and H > 0 and H*H < d

def zero_query(bits):
    # Invoke only after a valid paid all-zero regime/source-class certificate.
    parse(bits,3)
    return (0,0,0),0

def setup_instance(kappa, E):
    kappa, E = Q(kappa), Q(E)
    assert 0 <= kappa < 1 and E > 0
    T, rpower = 0, Q(1)
    while rpower > E/2:
        T, rpower = T+1, rpower*kappa
    J = 3
    while fib(J-2) < T:
        J += 1
    N = fib(J)
    B = Q(2)**(N+1)*(9+N)
    e_star = min(Q(1),(E/(2*B))**2)
    return {'J':J,'p':output_precision(E/2),'b':producer_precision(e_star),
            'e_star':e_star,'N':N}

def finite_guard_round(raw_integer, b):
    # raw_integer is the paid (b+4)-fractional-bit coordinate approximation.
    return round_num((raw_integer,b+4),b)

def parse_unbounded(bits):
    j, seen = 0, False
    for digit in bits:
        if digit not in ('0','1') or (not seen and digit != '1'):
            raise ValueError('invalid binary query')
        seen = True
        j = 2*j+int(digit)
    if not seen or j < 3:
        raise ValueError('future query must be at least 3')
    return j

def rational_kernel(replies, j):
    # Same squared-norm polynomial on the EXACT finite rational presentation class.
    assert len(replies) == 3 and all(len(v) == 3 for v in replies) and j >= 3
    y0,y1,y2 = (tuple(Q(c) for c in v) for v in replies)
    def dq(x,y):
        return sum((a*b for a,b in zip(x,y)),Q(0))
    w = tuple(y2[i]*y1[k]-y2[k]*y1[i] for i,k in ((1,2),(2,0),(0,1)))
    d = dq(y0,w)
    s = (d > 0)-(d < 0)
    z = tuple(s*c for c in w)
    u,v = dq(y1,y1),dq(y2,y2)
    a,c = fib(j-2),fib(j-1)
    if j % 3 == 1:
        m,n,anchor = (a-1)//2,c//2,y1
    elif j % 3 == 2:
        m,n,anchor = a//2,(c-1)//2,y2
    else:
        m,n,anchor = (a-1)//2,(c-1)//2,z
    coefficient = u**m*v**n
    return tuple(coefficient*x for x in anchor)

def setup_name_query(hbar, j, E):
    # ONLY the separately paid reusable Cauchy-name extension.
    hbar,E = Q(hbar),Q(E)
    assert hbar >= 1 and j >= 3 and E > 0
    R = hbar+1
    P = 3*hbar*hbar+3*hbar+1
    Cs = 2*hbar+1+2*hbar*P
    N = fib(j)
    B = R**(N+1)*(Cs+N)
    e_star = min(Q(1),(E/(2*B))**2)
    return {'j':j,'b':output_precision(e_star),'p':output_precision(E/2),
            'e_star':e_star,'N':N,'B':B}

def named_query(read_name, bits, E):
    # read_name(b) is a CHARGED finite access to the three already supplied names.
    # Its nine integers certify simultaneous vector error <= 2**(-b).
    # This callback does not exist in the original stopped finite-record interface.
    j = parse_unbounded(bits)
    coarse = read_name(0)
    assert len(coarse) == 9
    hbar = max(1,max(sum(abs(coarse[3*i+k]) for k in range(3))+1
                     for i in range(3)))
    cfg = setup_name_query(hbar,j,E)
    nums = read_name(cfg['b'])
    assert len(nums) == 9
    return round_vec(kernel(nums,cfg['b'],j),cfg['p']),cfg['p']
```

## 63. 准确有限核验与复现

以下完整代码保存为与 `reference.py` 同目录的 `verify.py`，运行 `python3 verify.py`。它枚举1–5叶的550棵实际有序树和6个固定制备，检查字面节点求值、原替换／解释运输、多项式核与实际投影不等式；另核验零、极小、报告符号零／错误符号、不在实际像中的非正交报告、长请求、舍入边界、范数包络、逐实例和名字接口，以及达到阈值的支撑覆盖和字面树。四个准确有理平方根尖锐对分别由两个真实树及同次固定准备实现；它们不来自任意环境三元组。

```python
import json
from fractions import Fraction as Q
from pathlib import Path
import reference as R

def cx(x,y):
    return tuple(x[i]*y[k]-x[k]*y[i] for i,k in ((1,2),(2,0),(0,1)))
def dp(x,y): return sum(a*b for a,b in zip(x,y))
def ev(t,p):
    if t == 'a': return p[0]
    if t == 'b': return p[1]
    return cx(ev(t[0],p),ev(t[1],p))
def sub(t):
    if t == 'a': return 'b'
    if t == 'b': return ('b','a')
    return (sub(t[0]),sub(t[1]))
def F(p): return p[1],cx(p[1],p[0])
def read3(t,p):
    a=[]
    for _ in range(3):
        a.append(ev(t,p));p=F(p)
    return a
def nums(y,b):
    out=[]
    for v in y:
        for x in v:
            z=Q(x)*(1 << b)
            assert z.denominator==1
            out.append(z.numerator)
    return out
def value(x): return tuple(Q(a,1 << b) for a,b in x)
def err2(x,y): return dp(tuple(a-b for a,b in zip(x,y)),tuple(a-b for a,b in zip(x,y)))
trees={1:['a','b']}
for n in range(2,6):
    trees[n]=[(s,t) for k in range(1,n) for s in trees[k] for t in trees[n-k]]
preps=[((Q(1),0,0),(0,Q(1),0)),((Q(1,2),0,0),(0,Q(3,4),0)),
       ((Q(1),Q(1),0),(Q(1),0,Q(1))),((Q(2),0,0),(Q(3),0,0)),
       ((0,0,0),(0,Q(1),0)),((Q(1),Q(1),0),(0,0,0))]
total=0
for group in trees.values():
    for t in group:
        for p in preps:
            y=read3(t,p); n=nums(y,32)
            pp=p
            for j in range(12):
                x=ev(t,pp)
                if j>=3:
                    assert value(R.kernel(n,32,j))==x
                    assert R.rational_kernel(y,j)==x
                if j<=3 and len(group)<100:
                    tt=t
                    for _ in range(j): tt=sub(tt)
                    assert ev(tt,p)==x
                pp=F(pp)
            w=cx(y[2],y[1])
            assert abs(dp(y[0],w))>=dp(y[2],y[2])
            assert dp(y[2],y[2])<=dp(y[0],y[0])*dp(y[1],y[1])
            total+=1

# Exact integer square-root enclosure, output boundaries and ties.
for n in range(1001):
    t=R.isqrt(n);assert t*t<=n<(t+1)*(t+1)
for n in range(-100,101):
    for b in range(7):
        for p in range(7):
            k=R.round_num((n,b),p)
            assert abs(Q(k,1 << p)-Q(n,1 << b))<=Q(1,1 << (p+1))
for p in range(12,17):
    v=tuple((k,12) for k in (3,4,5))
    lo,hi=R.norm_interval(v,p)
    sq=R.dot(v,v)
    assert Q(lo[0],1 << lo[1])**2<=Q(sq[0],1 << sq[1])<Q(hi[0],1 << hi[1])**2

# Stable uniform-cutoff arithmetic, and every finite head phase.
cfg=R.setup_stable(Q(1),Q(3,4),Q(1,8))
p=((Q(1,2),0,0),(0,Q(1,2),0));y=read3('a',p);n=nums(y,cfg['b'])
pp=p
for j in range(cfg['J']+8):
    x=ev('a',pp)
    if j>=3:
        word,pout=R.stable_query(n,cfg['b'],cfg,iter(bin(j)[2:]))
        assert err2(tuple(Q(k,1 << pout) for k in word),x)<=Q(1,8)**2
    pp=F(pp)
assert cfg['R']**cfg['T']<=Q(1,16)
assert R.fib(cfg['J'])>=cfg['T']
assert R.parse(iter('1'+'0'*100000),cfg['J'])[0]==cfg['J']
assert R.parse(iter('1'+'0'*100000),3)[1]==pow(2,100000,3)
for bad in ['', '0','01','10','1x','0011']:
    try: R.parse(iter(bad),cfg['J'])
    except ValueError: pass
    else: raise AssertionError(bad)

# Tiny actual wrong-sign and off-image report corners.
p=((Q(1,1 << 30),0,0),(0,Q(1,1 << 30),0));y=read3('a',p)
y[0]=tuple(-a for a in y[0]);b=100;n=nums(y,b)
z=value(R.anchors(n,b)[2]);x3=ev('a',F(F(F(p))))
assert dp(z,x3)<0
e=Q(1,1 << 29)
assert err2(z,x3)<=81*e

# Plateau polynomial/weighted words on all tested admissible sources.
plateau_checks=0
for t in trees[5]+trees[1]:
    p=((Q(1,2),0,0),(0,Q(3,4),0));y=read3(t,p);n=nums(y,32)
    pc=R.setup_plateau(n,32,Q(1,8));wc=R.setup_weighted(n,32,40,40)
    pp=p
    q3=ev(t,F(F(F(p))))
    for j in range(18):
        x=ev(t,pp)
        if j>=3:
            for c in (pc,wc):
                word,pout=R.plateau_query(c,iter(bin(j)[2:]))
                assert err2(tuple(Q(k,1 << pout) for k in word),x)<=Q(5,8)**2
        pp=F(pp)
    plateau_checks+=1

# Exact indexing check of the canonical PC2 phase and rotations.
qrot=((Q(3,5),Q(4,5),0),(Q(-4,5),Q(3,5),0))
assert ev('a',F(F(F(qrot))))==qrot[0]
assert ev('a',F(F(qrot)))==(0,0,-1)
assert ev('a',F(F(F(F(qrot)))))==qrot[1]

# Conditional budgets, certificates and finite guard rounding.
assert R.verify_conditioned_certificate(2,1,Q(1,4))
assert not R.verify_conditioned_certificate(2,1,Q(1,2))
assert R.verify_zero_certificate(2,2,1)
assert not R.verify_zero_certificate(2,2,Q(3,2))
assert R.zero_query(iter('11'))==((0,0,0),0)
assert R.parse_unbounded(iter('1011'))==11
for b0 in range(6):
    for raw in range(-200,201):
        nout=R.finite_guard_round(raw,b0)
        assert abs(Q(nout,1 << b0)-Q(raw,1 << (b0+4)))<=Q(1,1 << (b0+1))
icfg=R.setup_instance(Q(1,4),Q(1,8))
p=((Q(1,2),0,0),(0,Q(1,2),0));y=read3('a',p)
ns=nums(y,icfg['b']);pp=p
for j in range(icfg['J']+5):
    x=ev('a',pp)
    if j>=3:
        word,pout=R.stable_query(ns,icfg['b'],icfg,iter(bin(j)[2:]))
        assert err2(tuple(Q(k,1 << pout) for k in word),x)<=Q(1,8)**2
    pp=F(pp)
def finite_name(b0):
    return [R.round_num((int(c*16),4),b0) for v in y for c in v]
for j in range(3,8):
    word,pout=R.named_query(finite_name,iter(bin(j)[2:]),Q(1,8))
    pp=p
    for _ in range(j):pp=F(pp)
    assert err2(tuple(Q(k,1 << pout) for k in word),ev('a',pp))<=Q(1,8)**2
for cc in (None,Q(1,4)):
    wc=R.setup_weighted_budget(nums(y,8),8,Q(1,8),cc)
    assert wc['e_star']>0 and wc['norm_p']>=8
# Strict interior of actual nearest-dyadic cells, unaffected by any tie rule.
for b0 in range(8):
    h=Q(1,1 << b0);t0=h/32
    c=(1-t0*t0)/(1+t0*t0);s=2*t0/(1+t0*t0);lam=1-h/64
    pp=((lam*c,lam*s,0),(-lam*s,lam*c,0))
    yy=read3('a',pp)
    U=((1,0,0),(0,1,0),(0,0,-1))
    for v,w0 in zip(yy,U):
        for a,z0 in zip(v,w0):
            assert abs(a-z0)<h/4
            rounded=Q(a)/h+Q(1,2)
            assert rounded.numerator//rounded.denominator==z0*(1 << b0)

# Attained threshold certificate, covering every potentially improving composition.
assert 559**2<5*250**2 and 2**103411>6**40000
best=Q(2);mins=[];supported=0
for m in range(1,81):
    for n0 in range(1,81-m):
        if m%2==0 and n0%2==0:continue
        supported+=1
        if m>n0:
            assert Q(m+n0)-Q(n0*n0,m)>m
            continue
        q0=Q(6)**m/Q(3)**n0;q1=Q(2)**n0/Q(3)**m
        h=max(q0,q1,q0*q1)
        if h<best:best=h;mins=[(m,n0)]
        elif h==best:mins.append((m,n0))
assert supported==2380 and best==Q(32,27) and mins==[(3,5)]
t=('b','a')
for a in ['a','a','b','b','b','b']:t=(a,t)
p=((Q(6),0,0),(0,Q(1,3),0));pp=p;actual=[]
for _ in range(4):actual.append(ev(t,pp));pp=F(pp)
assert actual==[(0,0,Q(8,9)),(Q(-32,27),0,0),(0,Q(-256,243),0),(0,0,Q(8192,6561))]
evidence={'exact_tree_preparation_histories':total,'trees':sum(map(len,trees.values())),
          'preparations':len(preps),'future_kernel_indices':[3,11],
          'plateau_histories':plateau_checks,'plateau_indices':[3,17],
          'stable_cfg':{k:str(v) for k,v in cfg.items()},'long_query_bits':100001,
          'sqrt_integer_cases':1001,'rounding_cases':201*49,
          'threshold_supported':supported,'threshold':str(best),'threshold_minimizers':mins,
          'pc2_index_check':{'alpha_unit_x3':[1,0,0],
                              'correct_phase':'j congruent to 0 modulo 3'},
          'additional_contract_checks':{'guard_rounding_cases':2406,
              'certificate_checks':4,'instance_queries':'head and five tail samples',
              'cauchy_name_extension_queries':5,'strict_actual_dyadic_cells':8},
          'status':'finite falsifiers passed; universal claims depend on ordinary proofs'}
# Jointly actual rational sharp pairs, plus reported zero/sign/off-image corners.
sharp_pairs = []
for M in (4,8,16,32):
    s0, r0, N0 = Q(1,M*M), Q(M,2), Q(M**5,2)
    C0 = s0*(N0*N0-1)/(2*N0)
    co, si = (C0*C0-s0*s0)/(C0*C0+s0*s0), 2*C0*s0/(C0*C0+s0*s0)
    a0,b0 = (C0/r0,s0/r0,Q(0)), (r0,Q(0),Q(0))
    b1 = (r0*co,r0*si,Q(0))
    V1 = (r0*s0*si,-r0*s0*co,Q(0))
    a1 = tuple(C0/(r0*r0)*c+v/(r0*r0) for c,v in zip(b1,V1))
    t0,t1 = ('a',('a','b')), (('a','b'),'a')
    yy0,yy1 = read3(t0,(a0,b0)),read3(t1,(a1,b1))
    assert yy0[:2] == yy1[:2]
    assert dp(a0,a0)==dp(a1,a1) and dp(b0,b0)==dp(b1,b1)
    assert dp(a0,b0)==dp(a1,b1)
    assert dp(yy0[0],yy0[0]) <= 1
    assert dp(yy0[1],yy0[1])==Q(1,16)
    assert dp(yy0[2],yy0[2]) < Q(1,4)
    q2 = r0*s0**3
    eps = 4*q2*N0/(N0*N0+1)
    assert err2(yy0[2],yy1[2])==eps**2
    xx0=ev(t0,F(F(F((a0,b0)))))
    xx1=ev(t1,F(F(F((a1,b1)))))
    target = 2*Q(1,4)*q2*(N0*N0-1)/(N0*N0+1)
    assert err2(xx0,xx1)==target**2
    sharp_pairs.append({'M':M,'record_distance':str(eps),
                        'future_distance':str(target),
                        'future_squared_over_record':str(target**2/eps)})

adversarial_cases = []
p0=((Q(1,2),0,0),(0,Q(3,4),0))
y_true=read3('a',p0)
e0=Q(1,1<<24)
signs=((1,-1,1),(-1,1,1),(1,1,-1))
y_bad=[tuple(c+sgn*e0/4 for c,sgn in zip(v,z0))
       for v,z0 in zip(y_true,signs)]
assert dp(y_bad[1],y_bad[2]) != 0  # off actual nonzero orthogonal tail image
adversarial_cases.append(('nonorthogonal-off-image','a',p0,y_bad,e0))
p_tiny=((Q(1,1<<30),0,0),(0,Q(1,1<<30),0))
y_tiny=read3('a',p_tiny)
adversarial_cases.append(('tiny-wrong-sign','a',p_tiny,
                          [tuple(-v for v in y_tiny[0]),y_tiny[1],y_tiny[2]],Q(1,1<<29)))
adversarial_cases.append(('tiny-reported-sign-zero','a',p_tiny,
                          [(0,0,0),y_tiny[1],y_tiny[2]],Q(1,1<<30)))
p_zero=((Q(1,2),0,0),(0,Q(1,2),0))
y_zero=[tuple(sgn*e0/4 for sgn in z0) for z0 in signs]
adversarial_cases.append(('zero-source-off-image',('a','a'),p_zero,y_zero,e0))
for label,t0,p0,y_report,e0 in adversarial_cases:
    true=read3(t0,p0)
    assert all(err2(v,w0)<=e0**2 for v,w0 in zip(true,y_report))
    nn=nums(y_report,100)
    z=value(R.anchors(nn,100)[2])
    x3=ev(t0,F(F(F(p0))))
    assert err2(z,x3)<=17**2*e0
    assert e0<=cfg['e_star']
    pp=p0
    for j in range(cfg['J']+5):
        x=ev(t0,pp)
        if j>=3:
            word,pout=R.stable_query(nn,100,cfg,iter(bin(j)[2:]))
            assert err2(tuple(Q(k,1<<pout) for k in word),x)<=Q(1,8)**2
        pp=F(pp)
evidence['joint_actual_sqrt_pairs']=sharp_pairs
evidence['adversarial_report_cases']=[case[0] for case in adversarial_cases]
evidence['executed_scope']='literal all-tree samples, exact rational arithmetic, contracts and boundary witnesses only'
Path('evidence.json').write_text(json.dumps(evidence,ensure_ascii=False,indent=2))
print(json.dumps(evidence,ensure_ascii=False))
```

命令 `python3 verify.py` 的退出码为0，准确结果如下。该数据只核验所列有限实例、索引、程序分支及有证明覆盖的阈值算术；不替代第50–61节的全称普通证明，不认证现实传感／动作精度，也不产生 Lean 状态。

```json
{
  "exact_tree_preparation_histories": 3300,
  "trees": 550,
  "preparations": 6,
  "future_kernel_indices": [
    3,
    11
  ],
  "plateau_histories": 450,
  "plateau_indices": [
    3,
    17
  ],
  "stable_cfg": {
    "J": "8",
    "T": "21",
    "p": "4",
    "b": "22",
    "e_star": "1/1364224",
    "K": "73",
    "R": "7/8"
  },
  "long_query_bits": 100001,
  "sqrt_integer_cases": 1001,
  "rounding_cases": 9849,
  "threshold_supported": 2380,
  "threshold": "32/27",
  "threshold_minimizers": [
    [
      3,
      5
    ]
  ],
  "pc2_index_check": {
    "alpha_unit_x3": [
      1,
      0,
      0
    ],
    "correct_phase": "j congruent to 0 modulo 3"
  },
  "additional_contract_checks": {
    "guard_rounding_cases": 2406,
    "certificate_checks": 4,
    "instance_queries": "head and five tail samples",
    "cauchy_name_extension_queries": 5,
    "strict_actual_dyadic_cells": 8
  },
  "status": "finite falsifiers passed; universal claims depend on ordinary proofs",
  "joint_actual_sqrt_pairs": [
    {
      "M": 4,
      "record_distance": "1/262145",
      "future_distance": "262143/1073745920",
      "future_squared_over_record": "68718952449/4398063288320"
    },
    {
      "M": 8,
      "record_distance": "1/268435457",
      "future_distance": "268435455/35184372219904",
      "future_squared_over_record": "72057593501057025/4611686035607257088"
    },
    {
      "M": 16,
      "record_distance": "1/274877906945",
      "future_distance": "274877906943/1152921504611041280",
      "future_squared_over_record": "75557863725364567605249/4835703278476108884869120"
    },
    {
      "M": 32,
      "record_distance": "1/281474976710657",
      "future_distance": "281474976710655/37778931862957295927296",
      "future_squared_over_record": "79228162514263774643590529025/5070602400912935620385322303488"
    }
  ],
  "adversarial_report_cases": [
    "nonorthogonal-off-image",
    "tiny-wrong-sign",
    "tiny-reported-sign-zero",
    "zero-source-off-image"
  ],
  "executed_scope": "literal all-tree samples, exact rational arithmetic, contracts and boundary witnesses only"
}
```

## 追加锚（本行以下为增补区）
## 64. 每源有限的完整未来字与合法取得

本节至第74节研究定义1.1的全部非空有限有序树，仍取原三维定向叉积、$\rho\alpha=\beta$、$\rho\beta=\langle\beta,\alpha\rangle$。一次执行的所有叶、所有版本使用同一制备 $p=(a,b)$；比较来源时允许两次执行有不同制备。记 $x_j=E_p(\rho^jt)$、$q_j=|x_j|$、$W=(x_0,x_1,x_2)$，目标始终为共同坐标系中全部 $j\ge3$ 的向量，误差为 $\sup_{j\ge3}|\widehat x_j-x_j|$。原参数域仍是定义16.1的 $\mathcal D_{L,H,d_0}$，$L,H>0$、$0<d_0<L^4$。树大小无统一上限。

**定义 64.1（完整字及四种表示）。** 固定容差 $E>0$。源感知编码是集合函数 $a_E:\mathcal D\to\{0,1\}^*$，可使用实际来源的全部数学信息；它自身未必可执行。每源有限只要求每个 $a_E(s)$ 有限，固定完整字上限还要求 $\sup_s|a_E(s)|<\infty$。有效编码须另声明输入表示并以有限计算产生字。有限取得则要求观察者只通过明确获准的动作、回复及停止，实际得到这个字。

完整字包括全部源相关数值、程序选择、分支、精度、证书、输出格式、来源／坐标系／历史版本及动作／Stop 元数据。源无关的程序、解释器和算术库可以固定安装，但其保留成本另计；若复制进字则计入字长。不能把来源相关建议移到所谓安装程序中。以下可执行构造使用收费的有限有理容差 $0<\epsilon\le E$；为简化公式将其也记作 $E$。若容差本身以名字输入，取得这样一个正有理下界要另付费；粗平台分支还须取得 $1/2<E'\le E$，只在严格 $E>1/2$ 时存在这一选择。

准确有限有理三元组是一个闭合有限输入字；准确任意实寄存器没有有限位表示保证；可继续精化的名字是持续输入能力。三者不同。闭合字的解码器仍可在每个有限查询上使用随查询增长的工作空间和输出，闭合不等于固定有限状态。

**约定 64.2（原动作与扩展）。** 原动作只有 `Read0, rho, Read1, rho, Read2, Stop`，停止时真实来源位于 $\rho^2t$。它不提供叶、树码、计数、制备、复位、校准、准确实数相等／符号测试、停止后的精度请求或时延侧信道。有限近似回复、真有理回复、历史名字捕获和来源证书分别是需要收费及承诺的接口。以下任何扩展的正结论都以其接口为条件；原有限回复的障碍仍成立。

**复用 64.3（实际核与来源约束）。** 本卷定理3.1、4.3、5.1、推论16.3及引理26.1／第50节给出运输、全树符号、实际计数和准确核，直接用于下文。其成立对象是实际树历史。令 $F_0=0,F_1=1$，$a_j=F_{j-2},b_j=F_{j-1}$；$j\ge3$ 时

$$
x_j=\begin{cases}
q_1^{a_j-1}q_2^{b_j}x_1,&j\equiv1\pmod3,\\
q_1^{a_j}q_2^{b_j-1}x_2,&j\equiv2\pmod3,\\
q_1^{a_j-1}q_2^{b_j-1}x_3,&j\equiv0\pmod3,
\end{cases}\qquad
x_3=\operatorname{sgn}\bigl(x_0\cdot(x_2\times x_1)\bigr)(x_2\times x_1).
$$

取 $0^0=1$、$\operatorname{sgn}(0)=0$，零标签和依赖制备均在其适用范围内。实际约束为

$$|x_0\cdot(x_2\times x_1)|\ge q_2^2,\quad q_2\le q_0q_1,\quad
|x_0\cdot(x_2\times x_1)|\ge c q_0|x_2\times x_1|,\quad c=\sqrt{d_0}/L^2.$$

第三式使用原叶／行列式域；前两式对任意实际制备成立。有限报告可以不正交、不在实际像中，不能要求它们满足这些真来源约束。第68节只在误差证明中对真值使用约束。

## 65. 完整十制度及表示与取得的不同端点

**定理 65.1（平台的逐源字）。** 在原行3、5，未来或者全零／严格趋零，或者准确单位三周期。中性来源当且仅当 $q_1=q_2=1$；行3存在中性来源，行5存在中性来源当且仅当 $d_0\le1$，包括等号。每个固定 $E>0$ 都有一个固定可计算解码程序和一个源感知编码，为每个来源分配有限完整字并达到全未来误差 $E$。两个完整平台的 $E=0$ 都不能由可数有限字完成。

证明。行3由两叶范数不超过1和叉积范数不等式的结构归纳，所有替换树值均不超过1；行5由 $H=1$ 给三读界。因此 $q_0,q_1,q_2\le1$。非零尾有

$$q_j=(q_1q_2)^{F_{j-2}}q_2^{F_{j-1}-F_{j-2}}.$$

若 $q_1q_2<1$ 则趋零；否则两因子都是1，方向由实际核三周期。设原计数为 $(m,n)$、$r=|b|,s=\sqrt\Delta$。实际幅度式为 $q_1=r^ms^n,q_2=r^ns^{m+n}$；中性给两个对数方程，其行列式 $D=m^2+mn-n^2$ 是非零整数。$n=0$ 时直接成立；$n>0$ 时 $D=0$ 会令有理 $m/n$ 等于 $X^2+X-1$ 的无理根。故 $r=s=1$、$\Delta=1$。又实际投影至少 $q_2/q_1=1$、$q_0\le1$，迫使 $x_0=x_3$ 且 $q_0=1$；三个向量为有符号正交单位三周期。$\alpha$ 在 $(e_1,e_2)$ 处提供允许的中性成员，正好解释 $d_0\le1$ 的边界。制备的 $|a|^2$ 和 $a\cdot b$ 不因此都等于1和0。

趋零来源选有理 $q_1q_2<\kappa<1$，再选有限 $T,J$ 使 $\kappa^T\le E/2,F_{J-2}\ge T$。存 $J$ 和有限多个 $x_3,\ldots,x_{J-1}$ 的误差至多 $E/2$ 的 dyadic 近似，后来头部查表、尾部输出零。零尾也可取此法。中性来源存三个周期向量的误差至多 $E$ 的近似，按模3解码。标签、表、所选精度和来源元数据全部计入字；安装程序统一。这里选取精确分支的是源感知集合函数，并未从有限报告推断中性。

零误差障碍必须使用合法非零来源：行3可取单位来源；行5的全部参数，包括 $d_0>1$，由第66节的允许严格收缩族供应一个 $x_3\ne0$ 的成员。将这个固定实际来源的两叶同时作 $SO(3)$ 旋转，不改变树、叶界、行列式和读界；$x_3$ 遍历正半径的不可数球面。每个有限字只决定一个 $j=3$ 输出，可数个字不能准确区分该球面。证明没有把不允许的单位来源放入 $d_0>1$ 的域。

**定理 65.2（准确有理字与全实增长）。** 若原三读真正承诺准确有限有理坐标，则九个分子／分母和固定核是一个闭合有限完整字，在全部十制度中对每个有限 $j$ 准确输出，误差上确界为零。其工作和通常数值输出宽度随 $j$ 无界。全实增长行6、8、10不能由每源有限字在每个来源上达到有限全未来误差，即使容许有限误差界依源而变。持续名字可以逐个有限 $(j,E)$ 求值，但该名字是持续输入。

证明。有理点积、叉积、符号、整数 Fibonacci 和非负整幂都是有限准确运算；第64节的半指数由 Fibonacci 模2周期保证整数，所以有理核无需真实范数平方根。九个有理数一次存全，后续查询不再读取来源。若其总输入位宽为 $B$，安全中间／输出位宽为 $O(F_j(B+1)+j)$。这正是第58节准确有理表示的结论，逐查询无界成本不改变闭合性。增长障碍准确复用定理57.1：每行包括达到的 $H=H_*$ 都有合法非零增长源；绕 $x_1$ 旋转两叶形成不可数个两两全未来距离无穷的同树来源。两个来源若同字且各自误差有限 $E(s),E(s')$，其逐时距离被和界住，矛盾。有理呈现的可数子类没有这个不可数分离族，因此不受该结论排除。名字的逐查询构造和费用复用第58节第三项，不能改称闭合字或全实增长解法。

**制度对应 65.3。** 令 $D_{crit}=L^{2/\varphi^2}$、$\varphi=(1+\sqrt5)/2$。以下所有条件和模量证明精确复用定理24.2及第53节；表仅给新增取得结论的路由，证明见所指章节。

| 65行 | 完整原条件 | 全未来及有限表示／取得 |
| --- | --- | --- |
| 65行1 | $L<1$，任意 $H>0$ | 线性；每个 $E>0$ 可经付费有限精度与有理收缩上界取得；复用52.1 |
| 65行2 | $L=1,H<1$ | 同行1 |
| 65行3 | $L=1,H\ge1$ | 平台；逐源字适用于每个 $E>0$；统一完整字上限及原一次有限回复取得恰在 $E>1/2$；小容差全域名字取得失败 |
| 65行4 | $L>1,d_0<D_{crit},H<1$ | 同行1 |
| 65行5 | $L>1,d_0<D_{crit},H=1$ | 平台；固定 $0<E\le1/2$ 的全域名字有限取得当且仅当 $d_0>1$，点态终止而费用无统一界；每个 $E>1/2$ 全域粗取得成立 |
| 65行6 | $L>1,d_0<D_{crit},H>1$ | 全实增长有限字障碍；准确有理闭合字为受限例外 |
| 65行7 | $L>1,d_0=D_{crit},H\le1$ | 全零未来，包括 $H=1$；常零字，执行须有真实付费制度／来源证书 |
| 65行8 | $L>1,d_0=D_{crit},H>1$ | 同行6 |
| 65行9 | $L>1,d_0>D_{crit},H<H_*$ | 全零未来；同行7 |
| 65行10 | $L>1,d_0>D_{crit},H\ge H_*$ | 同行6，达到的等号也增长 |

全部行 $\Omega(0)=0$；三个线性行为小正误差的 $\Theta(\epsilon)$，两个平台保持充分小正区间的准确 $\Omega=1$、全局 $\Omega\le2$ 及 $\epsilon\ge2$ 时 $\Omega=2$，三个增长行为每个正误差的 $\Omega=\infty$。不新增平台中间完整曲线。所有非零全实行的 $E=0$ 障碍同样由一个允许非零来源的旋转在 $j=3$ 给出。准确有理例外适用于所有行；不是把非零全实域改为有理域。

**阈值复用 65.4。** $H_*$ 取定理18.4、19.1–19.3及第53节的实际支持组成优化，支持为两原叶及 $m,n>0$、非双偶的全部混合组成。保留最强的有限截止：令 $z=\log\sqrt{d_0},\ell=\log L,\gamma=z-\ell/\varphi^2>0$，任何可持平或改善叶上界 $z$ 的组成满足 $m+\varphi n\le z/\gamma=\varphi^2z/G$，$G=\varphi^2\gamma$。这是第53节由 $f_1+\varphi f_2\ge(m+\varphi n)G$ 得到的截止，第19.1节也给指定 $h$ 的 $h/\gamma$ 截止。较宽 $\varphi z/\gamma$ 只为充分列表，不替代较小列表。仍对每个候选测试完整三线的区间端点和交点，阈值由真实树／正交制备达到；定理31.1的 $H_*(6,4)=32/27$ 和八叶达到者直接复用。这些实参数数学分类不产生任意实相等的有效判定器。

## 66. 两种准确近中性来源与有理归一化

**定理 66.1（固定行列式及准确首读）。** 在行5的每个完整参数域，选

$$\max(1,\sqrt{d_0})<s_*<L^{1/\varphi^2},\quad D_* =\log s_*>0.$$

令 $k$ 为正的6倍数，$T_k=\rho^k\alpha$，$m=F_{k-1},n=F_k,d=n-m=F_{k-2}$，供应同一次执行的制备

$$p_k=(s_*^{n/d}e_1,s_*^{-m/d}e_2),\qquad v_k=s_*^{-1/d}.$$

全部足够晚成员属于原域，其准确记录是 $(e_1,v_ke_2,-v_ke_3)$，$\Delta=s_*^2$ 恒定，$x_j=v_k^{F_j}U_j$，$U_j$ 按 $j\bmod3$ 为 $(e_1,e_2,-e_3)$。每个成员严格趋零，三读趋 $U$；当 $d_0>1$，$U$ 不在实际记录像中。

证明。原有序递推给 $T_{k+2}=\langle T_{k+1},T_k\rangle$、组成 $(m,n)$ 和叶数 $N_k=F_{k+1}$；$k\equiv0\pmod6$ 给单位标签 $+e_1$。不变量 $I(m,n)=n^2-mn-m^2$ 经计数更新变号，从 $(1,0)$ 的值 $-1$ 出发，在偶 $k$ 仍为 $-1$。正交同次制备按原叶次数齐次，故 $q_0=1$；实际尾式给

$$\log q_1=\left(n-\frac{m^2}{d}\right)D_*=-D_*/d,\qquad \log q_2=-D_*/d.$$

其方向正好为 $e_2,-e_3$，递推给全部未来式。两叶积为 $s_*$，$|b|<1<L$，$n/d\to\varphi^2$，故 $|a|\to s_*^{\varphi^2}<L$；行列式恒大于 $d_0$，三读范数 $1,v_k,v_k\le1$。所有联合来源约束同时成立。$D_*/d\to0$，且 $z/2\le1-e^{-z}\le z$ 对充分小 $z>0$，所以 $1-v_k=\Theta(1/d)$；Binet 式给 $-\log_2(1-v_k)=k\log_2\varphi+O(1)$。第65.1节的中性判据排除 $d_0>1$ 时的极限。行3另用 $\alpha$ 的 $(e_1,ve_2)$，$\sqrt{d_0}\le v<1$，有完全同型记录／未来；其行列式为 $v^2$，不冒称恒定。

**定理 66.2（有理制备及准确常数）。** 行5选正有理数

$$\max(0,\tfrac12\log d_0)<c_*<\log L/\varphi^2.$$

沿同样的 $T_k,m,n,d$ 取 $u_k=1+c_*/d,\mu_k=u_k^{-1}$ 和 $p_k=(u_k^ne_1,u_k^{-m}e_2)$。全部足够晚成员合法，有理制备和准确记录 $(e_1,\mu_ke_2,-\mu_ke_3)$，$x_j=\mu_k^{F_j}U_j$。其行列式为 $u_k^{2d}$，一般随 $k$ 变化。置 $\widetilde g_k=1-\mu_k^2$、$g_k=1-q_1^2q_2^2=1-\mu_k^4$，则

$$N_k\widetilde g_k\longrightarrow2c_*\varphi^3,\qquad N_kg_k\longrightarrow4c_*\varphi^3.$$

前者是乘积幅度 $q_1q_2$ 距1的间隙；后者是平方乘积间隙。单个平方范数间隙 $1-q_2^2$ 在本族恰等于前者，一般来源没有这种相等。

证明。以 $u_k$ 为底，原树齐次求值的时刻 $h$ 指数为 $nF_{k+h-1}-mF_{k+h}$，初两值为 $0,-1$，遵守同一递推，故恰为 $-F_h$。这证明准确首读及全部未来，不只给三个边缘值。两叶长分别趋 $e^{c_*\varphi^2}<L,e^{-c_*\varphi}<1$，$\Delta\to e^{2c_*}>d_0$，三读为 $1,\mu_k,\mu_k$，故最终合法。$N_k/d\to\varphi^3$ 和 $d(1-(1+c_*/d)^{-r})\to r c_*$，取 $r=2,4$ 得两常数。

该族准确的全尾阈值为

$$J_k(E)=\min\{j\ge3:F_j\ge\log(1/E)/\log u_k\}\qquad(0<E<1).$$

因为 $F_j$ 在此范围单调，这是所有以后时刻的截止；若 $j=3$ 已足够即取3。$F_j=\Theta(\varphi^j)$、$\log u_k\sim c_*/d$ 给固定 $c_*,E$ 的 $J_k(E)=\log_\varphi N_k+O_{c_*,E}(1)$；阈值充分大时更一般为 $\log_\varphi(\log(1/E)/\log u_k)+O(1)$。这些式子表述数学来源，不是免费发给观察者的树／计数／制备口。

**例 66.3（全有理合法域）。** 取 $L=2,H=1,d_0=5/4,c_*=1/4$，每个正6倍数 $k\ge6$ 都合法。$n/d\le8/3$，$u_k^n<e^{2/3}<2$；其中 $\log2>2/3$ 可由 $\log2=2\sum_{h\ge0}(1/3)^{2h+1}/(2h+1)$ 的首项及正余项得到。$b<1$，Bernoulli 给 $\Delta=(1+1/(4d))^{2d}\ge3/2>5/4$。此域没有中性来源，仍逐点逼近单位记录。固定行列式族与本有理族各自保留其不同性质；第27.2、55节的临界指数缩放族仍按原式复用，不另复制完整构造。

## 67. 实际计数行列式的尖锐衰减律与付费大小证书

**定理 67.1（整数行列式的较强界）。** 行5且 $d_0>1$，令 $z_0=\log\sqrt{d_0}>0$。一个非零尾的原始实际组成 $(m,n)$、叶数 $N=m+n$ 满足

$$-\log q_2\ge\frac{z_0|m^2+mn-n^2|}{\max(m,n)}\ge\frac{z_0}{N},\qquad
q_j\le\exp\left(-\frac{z_0F_{j-1}}N\right)\quad(j\ge3).$$

零尾直接满足后一界。故整个尾输出零、误差至多 $E/2$ 的充分截止为 $F_{J-1}\ge N\log(2/E)/z_0$，$0<E\le1$，并有 $J=O(1+\log N+\log(1+\log(1/E)))$。

证明。置 $a=-\log q_1\ge0,b=-\log q_2$。来源约束 $q_2\le q_0q_1\le q_1$ 给 $b\ge a$。反解准确幅度的矩阵 $\left(\begin{smallmatrix}m&n\\n&m+n\end{smallmatrix}\right)$，有

$$\log s=\frac{na-mb}{D}\ge z_0,\quad D=m^2+mn-n^2\ne0.$$

非零整数给 $|D|\ge1$；$na,mb$ 是非负数，其差的绝对值至多两者的最大，故

$$z_0|D|\le|na-mb|\le\max(m,n)b.$$

这也涵盖两种原单叶组成。代入准确全未来幅度式、$q_1\le1$，得全尾界；Fibonacci 指数单调并按 $\Theta(\varphi^j)$ 增长给所述截止，未限制来源树大小。

**命题 67.2（阶的锋利性及边界）。** $1/N$ 衰减阶在同一域不可提高为统一较大阶，第66.1族有

$$N_k(-\log q_2)=N_kD_*/d\longrightarrow D_*\varphi^3>0.$$

第66.2有理族也给 $N_k(-\log q_2)\to c_*\varphi^3$。其最早全尾截止在 $0<E\le1/2$ 满足 $J_E=\log_\varphi N_k+\log_\varphi\log(1/E)+O(1)$，常数独立于 $k$ 和此范围的 $E$，由准确幅度式及 $d\log u_k\to c_*$ 得到。第27.2、55节指数缩放族还有准确常数：按其原记号 $C_*=\log a_*$、$\tau_k=2(1+C_*)\varphi^{-k}/N_k$、正12倍数 $k$，

$$N_k(-\log q_2)\longrightarrow\frac\varphi{\sqrt5}\left[2(1+C_*)\varphi^2-C_*/\varphi^2\right]>0.$$

证明只需代入原准确式 $-\log q_2=\tau_kF_{k+3}-C_*\varphi^{-k-2}$，以及 $N_k\varphi^{-k}\to\varphi/\sqrt5$、$F_{k+3}/N_k\to\varphi^2$。更一般 $j\ge3$，该式为 $\tau_kF_{k+j+1}-C_*\varphi^{-k-j}$。Binet 给首项在 $\varphi^j/N_k$ 的两个正常数之间，负项与首项的比例含 $\varphi^{-2j}$ 且 $2(1+C_*)>C_*$；故对全部足够晚 $k$、全部 $j\ge3$ 有 $-\log q_j=\Theta(\varphi^j/N_k)$，同样给所述全尾截止阶。使用已发表来源式不将原来源构造重算为新增内容。这里是来源衰减／截止律，尚未声称最优保留字长或总运行时间。

$d_0>1$ 是必要条件：行3的固定 $\alpha$、近单位缩叶有 $N=1$ 且收缩可任意慢。行5的 $d_0\le1$ 取固定单叶 $t=\beta$，$a=-e_3/r,b=re_1$、$1/L<r<1$，有 $\Delta=1$、记录 $(re_1,e_2,-re_3)$、$q_j=r^{F_{j-1}}$；$r\uparrow1$ 时 $N=1,-\log q_2\to0$。准确大小本身不能在这部分域给正收缩间隙。另一常用坐标制备 $(e_1/r,re_2)$ 是同一单叶 $\beta$ 族的 $SO(3)$ 像：将正向标架 $(-e_3,e_1,e_2)$ 送到 $(e_1,e_2,-e_3)$，准确记录变为 $(re_2,-e_3,re_1)$，所有范数／行列式／指数相同；它仍不同于两叶局部族。

**定理 67.3（读前大小证书的有限取得）。** 额外付费供方在第一次 Read 前给整数 $\overline N\ge N$、有理 $1<d_-\le d_0$ 和行5域的真实证书，绑定初始来源及版本。令

$$z_-=(d_--1)/(2d_-),\quad t_-=z_-/\overline N\in(0,1),\quad\kappa=1-t_-/2.$$

此证书给 $q_2\le\kappa<1$，亦给 $q_1q_2\le\kappa$。据第68节在读前选择一次付费报告精度，仍只作三读两更新 Stop，即可产生任意正容差的闭合字。

证明。$\log d_-\ge(d_--1)/d_-$（积分 $1/u$ 在 $[1,d_-]$ 的下界），故 $z_-\le z_0$。定理67.1给 $q_2\le e^{-t_-}\le1/(1+t_-)\le1-t_-/2$；最后式等价于 $t_-(1-t_-)\ge0$。零尾也成立。第68节的有理搜索因此终止并证明整个未来误差。更强的 $F_{J-1}$ 截止可以使用；主程序统一使用较保守的乘积证书 $F_{J-2}$ 截止，不删去定理67.1的较强结论。

真实性、发行、绑定和查验归供方；来源创建者可按有限树构造维护计数并支付节点／整数费用。原三读本身不能验证隐藏树的叶数，整数的语法正确不证明它是上界。若观察者另外取得完整树码去验证，是另一个收费端口。真实有限中性／全零／域证书也依此规则，不能由旧有限报告免费发行。

## 68. 平方范数裁剪核的全时间误差证明

**定理 68.1（主执行核）。** 设实际三读 $q_0,q_1,q_2\le1$，真付费有理证书 $q_1q_2\le\kappa<1$、$0\le\kappa<1$。同时有限报告满足 $|y_i-x_i|\le e\le1$，误差可相关且报告可在实际像外。计算

$$Z=\operatorname{sgn}(y_0\cdot(y_2\times y_1))(y_2\times y_1),\quad
\widehat U=\min(1,|y_1|^2),\quad\widehat V=\min(1,|y_2|^2).$$

在第64节三个相位中分别使用系数

$$\widehat U^{(a_j-1)/2}\widehat V^{b_j/2},\quad
\widehat U^{a_j/2}\widehat V^{(b_j-1)/2},\quad
\widehat U^{(a_j-1)/2}\widehat V^{(b_j-1)/2},$$

乘报告锚 $y_1,y_2,Z$，得 $\widehat P_j$。这些半指数都是非负整数。若 $e\le(1-\kappa^2)/12$，则全部 $j\ge3$ 同时有

$$|\widehat P_j-x_j|\le\left(9+\frac{18}{1-\kappa^2}\right)\sqrt e.$$

若额外付费给 $0<c_-\le\sqrt{d_0}/L^2$，还可用线性界

$$|\widehat P_j-x_j|\le\left(\max(1,16/c_-)+\frac{18}{1-\kappa^2}\right)e.$$

执行只需有限数的平方、叉积、点积、有限有理比较及整数幂，无真实实数范数、符号或相等端口。

证明。先证第三锚，精确复用第51节的机制并给此处常数。令 $w=x_2\times x_1,W'=y_2\times y_1$，双线性给 $|W'-w|\le B_e=(2+e)e\le3e$。真尾零或符号正确时锚差至多 $B_e$；错号或报出零号时

$$|x_0\cdot w|\le e|w|+(q_0+e)B_e\le7e.$$

实际桥 $q_2^2\le|x_0\cdot w|$ 给 $|w|=q_1q_2\le\sqrt{7e}$，于是反号误差 $2|w|+B_e\le9\sqrt e$。这覆盖极小真值、报零、错号及非正交像外报告。在有 $c_-$ 的分支，若 $q_0<2e$，$|w|\le q_0$ 给误差至多 $7e$；否则 $q_0\ge2e>0$，

$$c_-q_0|w|\le e|w|+(q_0+e)B_e\le q_0e+\tfrac32q_0B_e.$$

故 $2|w|+B_e\le16e/c_-$，因为 $c_-\le1$。$e=0$ 使用准确核，不作零分母推理。前两锚误差至多 $e$。

置 $U=q_1^2,V=q_2^2$。范数的1-Lipschitz性及 $|y_i|\le1+e$ 给 $||y_i|^2-q_i^2|\le3e$；标量裁剪到 $[0,1]$ 不增加到真值的距离，故 $|\widehat U-U|,|\widehat V-V|\le3e$。取包含两点的坐标矩形，其最大坐标均至多1；最大乘积为

$$\max(U,\widehat U)\max(V,\widehat V)\le UV+6e\le\kappa^2+6e\le\zeta=(1+\kappa^2)/2<1.$$

这里分别用每个坐标增量至多 $3e$ 以及另一最大坐标至多1。整条插值线段在此矩形中；只检查两端乘积不足以证明线段乘积界。

$j=3$ 的系数准确为1，$j=4$ 的系数为 $V$、误差至多 $3e$。对所有 $j\ge5$，三个相位的整数指数 $(p,q)$ 均满足 $1\le p\le q\le2p$。验证：$b_j=a_j+F_{j-3}\le2a_j$；相位1的 $j\ge7$ 有 $b_j\le2a_j-1$，$b_j$ 为偶数，故加强为 $b_j\le2a_j-2$，于是 $q\le2p$。相位0的 $j\ge6$ 用同一严格界；相位2用 $b_j\le2a_j$。$j=5,6,7$ 分别给 $(1,1),(1,2),(2,4)$；正性及 $q\ge p$ 随 Fibonacci 单调和模2周期成立。不能漏掉前两例外系数。

矩形上多项式 $C(u,v)=u^pv^q$ 的导数包括零边界均满足

$$|\partial_u C|\le p\zeta^{p-1},\qquad |\partial_v C|\le q\zeta^{p-1}.$$

例如前者为 $p(uv)^{p-1}v^{q-p+1}$，后者为 $q(uv)^{p-1}uv^{q-p}$，剩余因子均至多1。沿上述线段积分，系数差至多 $3e(p+q)\zeta^{p-1}\le9ep\zeta^{p-1}$。又

$$p\zeta^{p-1}\le\sum_{h=0}^{p-1}\zeta^h\le(1-\zeta)^{-1},$$

故系数差至多 $18e/(1-\kappa^2)$，也涵盖 $j=3,4$。真锚范数至多1、报告系数至多1；先变锚再变系数，误差不超过锚误差加系数差。$e\le\sqrt e$ 完成通用平方根界；条件分支完成线性界。证明统一覆盖全部树和无限多个未来时刻。

**推论 68.2（正整数预算及全尾闭合）。** 置 $h=1-\kappa^2$，通用 $K=9+18/h$ 或条件 $K=\max(1,16/c_-)+18/h$。分别选择

$$e_* =\min\{1,h/12,(E/(2K))^2\},\qquad
 e_* =\min\{1,h/12,E/(2K)\}.$$

从 $z=1,b=0$ 开始二分直到 $2^{-b}\le e_*$；从 $z=1,p=0$ 二分直到 $2^{-p}\le E/2$。从 $T=0,r=1$ 开始乘 $\kappa$ 直到 $r\le E/2$；从 $(J,F_{J-2},F_{J-1})=(3,1,1)$ 用整数加法直到 $F_{J-2}\ge T$。头部 $3\le j<J$ 计算上述核并舍入到 $p$ 位；整个 $j\ge J$ 输出零。

证明。所有预算都是正有理，二分终止；$\kappa<1$ 使乘法搜索终止，$\kappa=0$ 至多一次，$E\ge2$ 时 $T=0$。Fibonacci 搜索终止，$T\le1$ 时 $J=3$、头为空。第68.1节使头算术误差至多 $E/2$；每坐标最近 dyadic 舍入的向量误差至多 $\sqrt3\,2^{-p-1}<E/2$。真值全尾 $q_j\le\kappa^{F_{j-2}}\le E/2$，包括零尾。若 $T>1$，最小性给 $F_{J-3}<T,F_{J-2}<2T,F_J<6T$；因此

$$T=O\left(1+\frac{\log_+(1/E)}{1-\kappa}\right),\quad
J=O(1+\log(T+1)),\quad D=\max(2,F_J)=O(T+1),$$

$\log_+(r)=\max(0,\log_2r)$。精度为 $O(1+\log_+(1/E)+\log(1/h))$，条件分支另加 $\log(1/c_-)$，实际公共有理数字宽另计。上述算法在所有正 $E$、$\kappa=0$ 均定义，不能省掉加1或将 $E\ge1$ 排除。

## 69. 真实历史名字、首停余量及粗取得

**定义 69.1（所有合法名字）。** 扩展在原三次 Read 捕获其同一来源、同一共同坐标系和各自历史版本0、1、2的不可变名字。`NameRead(b)` 返回九整数 $n_{i,k}$，代表 $y_i=(n_{i,k}2^{-b})_{k=0}^2$，同时满足 $|y_i-x_i|\le2^{-b}$。单位读界的标准字母表为 $|n_{i,k}|\le2^b+1$；读界 $\bar H\ge1$ 改为 $\lceil\bar H2^b\rceil+1$。同一名字同一精度的回复固定；在全部精度满足此合同的每个映射都合法，正确性与点态终止量化所有这样的名字及所有允许误差相关。逐坐标最近 dyadic 舍入给至少一个名字，向量误差至多 $\sqrt3\,2^{-b-1}<2^{-b}$；这不证明供方可计算性或物理发行。

精化是额外收费服务，不改变真实来源、不重新 Read。每个有限请求须在有限时间回应，但没有统一延迟承诺。成功取得后关闭名字能力，后续解码只用完整字。源／坐标系／版本绑定、捕获、保管和认证都要付费。真中性、全零、大小及域证书是不同的有限付费输入；名字本身不供应准确实相等判定。

**定理 69.2（严格搜索的第一返回余量）。** 在严格域 $q_1q_2<1$，$g=1-q_1^2q_2^2\in(0,1]$。依次请求 $b=1,2,4,8,\ldots$，$e=2^{-b}$，计算

$$Q_i=\min(1,|y_i|^2+3e),\quad P=Q_1Q_2.$$

只在 $P+12e<1$ 时停止搜索，返回 $\kappa=(1+P)/2$。它对每个合法名字有限停止，且第一次实际返回就满足

$$q_1q_2\le\sqrt P\le\kappa<1,\qquad1-\kappa>g/4.$$

然后按第68.2节请求一次最终精度，保留有限字并关闭名字，即能完成严格域每个正容差的全未来任务。

证明。平方范数误差至多 $3e$ 给 $q_i^2\le Q_i\le q_i^2+6e$，且两者在 $[0,1]$；故 $0\le P-q_1^2q_2^2\le12e$。当 $e\le g/48$，$P+12e\le1-g+24e\le1-g/2<1$，与合法回复的选取无关。返回时 $\sqrt P\le(1+P)/2$ 由 $(1-\sqrt P)^2\ge0$；令 $\delta=P-q_1^2q_2^2$，停止条件给 $\delta\le12e<1-P$，于是 $g=(1-P)+\delta<2(1-P)$，从而 $1-\kappa=(1-P)/2>g/4$。这是返回当刻的证明，不能用某个以后足够细的精度替代首停读数。第68.2节此后全尾有限闭合。

取分析中的 $B=\max(1,\lceil\log_2(48/g)\rceil)$，可用将有理1逐次减半到 $g/48$ 的次数定义。观察者不知道 $g$，实际只运行停止测试。首成功 $b_s\le2B$，发现调用至多 $1+\lceil\log_2B\rceil$，精度总和小于 $2b_s\le4B$。因此标准九整数的数值回复共 $O(B)$ 位，精度标头及实际身份／格式宽另计；有理范数发现工作保守 $O((B+1)^3)$，暂存 $O(B+1)$。供方生成／访问的时间不由这些接收位数控制。首停余量给 $h=1-\kappa^2\ge1-\kappa>g/4$，最终

$$b_f=O(1+\log_+(1/E)+\log(1/g)),$$

条件分支另加 $\log(1/c_-)$。总调用为发现调用加一次，数值接收总位数 $O(B+b_f+1)$。$g=1$、全零尾及 $E\ge1$ 均包括在正的这些式子中；没有在 $g=1$ 处使用无意义的裸 $\log\log(1/g)$。

**命题 69.3（粗平台与真中性证书）。** 每个 $E>1/2$ 在两个完整平台都有统一有限精度的原三读取得，包括全部中性来源。每个 $E>0$ 在真实中性证书分支也有有限取得；它不从报告判中性。

证明。每相位的真未来是锚 $x_1,x_2,x_3$ 的 $[0,1]$ 倍，锚范数至多1，故半锚误差至多 $1/2$。以 $y_1/2,y_2/2,Z/2$ 替换，中心误差至多 $(9/2)\sqrt e$（额外条件可用 $8e/c_-$）。取 $\tau=E-1/2>0$、$e\le\min(1,(\tau/9)^2)$、输出误差至多 $\tau/2$，总误差至多 $E$。这是第54节半锚库的准确复用。只有有限个原始付费报告和三相位字，无未来精化。名字总算法在 $E>1/2$ 时直接走这个粗分支，不能误称严格搜索此时会在中性停止：中性 $P\ge q_1^2q_2^2=1$，严格搜索永不返回。

真中性证书给单位三周期；取 $e\le\min(1,(E/18)^2)$ 和输出误差至多 $E/2$，报告三个整锚的误差及舍入均满足 $E$。真全零证书直接用常零字；程序仍支付原动作和瞬态回复。证书语法和数值不等式检查不验证其来源真实性。第52.1节较宽稳定域 $q_0\le\bar H,q_1,q_2\le\rho<1$ 的无叶／Gram条件程序、平方根保证及定理21.3的实际尖锐对完整复用；不能把可选 $c_-$ 变成通用路线的必需条件。

## 70. 有限停止纤维与端点三点半径

**定理 70.1（相对于接口的取得判据）。** 确定性取得程序正确，当且仅当它每个合法停止叶的完整字同时服务该完整记录兼容的全部实际来源／名字／传感相关，并且误差不超过 $E$。有效全域取得还要求一个合法有效停止树覆盖每个合法执行。不可变名字接口中，一个可枚举的有限可靠圆柱族，附有效有限字并覆盖每个合法名字，也充分。

证明。同一完整记录导致同一动作选择和同一字，故必要。合法停止树到达可靠叶则给充分性。名字上的有限计算只读取有限请求／位，停止集合可枚举为有限圆柱并附算出的字；反向将圆柱的有限匹配测试交错执行，覆盖保证某个测试结束匹配，返回可靠字。这里圆柱可靠性是已给证明承诺，未声称其一般可判。只有不可变名字允许不改变被测值地交错请求；任意不可逆接口必须给合法停止树，抽象圆柱覆盖本身不授动作权。可数覆盖、直径至多 $2E$ 或泛泛连续性不足以构造字中心和合法停止。

**引理 70.2（急角三点半径及有序极限）。** $0<\theta<\pi/4$，$u_\pm=(\cos\theta,\pm\sin\theta,0)$。$\{0,u_+,u_-\}$ 的最小包围球半径为 $R_\theta=1/(2\cos\theta)>1/2$。

证明。中心投影到三点平面再与镜像平均，凸性不增加最大距离，故可取 $te_1$。$t<0$ 的单位点距离至少1；$t\ge0$ 时目标为 $\max(t,\sqrt{1+t^2-2t\cos\theta})$。两项交点 $t=R_\theta<\cos\theta$；交点左侧第二项至少 $R_\theta$，右侧第一项至少它，该中心达到此值。

实际使用此几何须固定次序。对一个相同记录纤维中的正负旋转近单位收缩族，先固定未来相位 $j$、令来源族索引趋无穷，迫使共同输出到两单位方向的距离至多 $E$。再固定同纤维的一个严格收缩成员，令 $j$ 沿该相位趋无穷，迫使输出范数的上极限至多 $E$。取有界子列极限才得到三点共同球；不能交换两极限。

**定理 70.3（原适应性一次有限回复仍失败）。** 两个完整平台的原三读一次有限回复界面，在每个固定 $0<E\le1/2$ 都不能保证有限停止的全未来有限字取得，即使三次精度和最终字长从之前回复适应选择、字长无事先上限。此结论适用于完整正误差球，及分别检查的最近真 dyadic 坐标仪器；对下述守护近似再舍入关系也成立。

证明。沿假设协议的单位回复路径 $U=(e_1,e_2,-e_3)$。行3取第66.1的 $\alpha$ 族；行5取第66.1或66.2的原 $T_k$ 族。这些实际严格收缩来源的三读趋 $U$，每个固定未来趋相应单位方向。即使 $U$ 在 $d_0>1$ 时不是真记录，每个已发出的有限单位回复前缀都由足够晚实际来源实现。协议若在这个前缀不作有限下一步，就在某个合法实际执行上不能终止。因此它须沿单位路径有限作下一读、更新和 Stop，最后是一个有限完整记录。

其三次正容差最小值为 $\delta>0$。取小 $\theta$ 并将整个族的两叶同时绕 $e_1$ 正向旋转 $\pm\theta$；叶／Gram／读界均保持，首读仍准确 $e_1$。所有足够晚旋转来源和一个固定未旋转晚成员都兼容同一完整单位报告及相同身份／动作元数据。每个固定 $j\equiv1\pmod3$ 的族极限是绕 $e_1$ 的 $e_2$ 正负旋转，两单位点与零构成引理70.2的等距三点。严格遵循该引理的极限次序，共同字必须有误差至少 $R_\theta>1/2$，矛盾。来源身份字段是合同中的共同外部标识，不能额外编码隐藏树或实制备。

最近真值仪器需单独确认单元：单位坐标在每个有限精度 $b$ 的格点中心。取单位路径所选三步的最小格距 $h_{min}>0$，$\theta<h_{min}/16$，再使 $1-v<h_{min}/16$。所有非恒定坐标到单位中心严格小于 $h_{min}/4$，首读不变，所以全部九格回复相同，平局规则无关。此前相同回复决定后续相同精度，完整纤维与三点论证成立。第56.2节较强的固定精度必要条件 $E=1/2+\tau\Rightarrow\tau\ge2^{-2b}/384$ 原样复用；此处新增的是适应路径，没有放宽固定精度结果。

守护生产者采用另一完整关系：请求 $b$ 时，先取得分母 $2^{b+4}$ 的三维守护近似，每向量误差至多 $2^{-b-4}$，再逐坐标最近舍入到 $b$。总向量误差至多 $(1/16+\sqrt3/2)2^{-b}<2^{-b}$。在允许所有合法守护回复的关系下，任何距单位向量至多 $2^{-b-4}$ 的真向量都允许单位守护回复，它舍入后仍为单位。对单位路径的三步取最小守护半径，令族和旋转足够接近，就得到同样完整纤维。这独立验证了这个生产者关系；别的确定性生产者若限制守护回复子集，必须核对自己的纤维，不能套用此单元证明。另一方面，若每个所到动作只准有界坐标／有界元数据的有限回复字母表，三读总协议有有限分支数、有限终字集；有限确定性后处理不能额外编码来源，定理55.1也排除 $E\le1/2$。准确无界长度有理回复和源感知证书没有这一有限字母表前提。

**定理 70.4（中性名字障碍和准确边界）。** 每个固定 $0<E\le1/2$，行3的全域普通名字取得失败；行5全域普通名字取得当且仅当 $d_0>1$。严格域有第69.2的点态全合法名字终止。每个 $E>1/2$ 的两个全平台则有第69.3的粗总取得。

证明。先对实际单位中性来源给一个合法名字，在每个精度回复准确 $U$。假设全域程序停止，有限请求有正最小半径；同路径的严格收缩、正负旋转族可选到该半径内，未请求精度补任意准确 dyadic，便成为同有限回复路径的合法名字。引理70.2及实际来源纤维排除 $E\le1/2$。这只须存在一个阻止全合法名字总性的合法中性名字，未声称每个中性名字都让某程序不停止。对任意非 dyadic 中性三标架也可选逐步严格内点的最近 dyadic 名字；一个有限路径的正余量最小值代替上述半径。

加入有限树码也不修复：行3可固定 $\alpha$，制备 $(\lambda e_1,\lambda e_2)$、$\lambda\uparrow1$，$\Delta=\lambda^4\ge d_0$，$q_j=\lambda^{F_{j+1}}$。行5 $d_0\le1$ 固定 $\beta$，制备 $(-e_3/r,re_1)$、$1/L<r<1$，$\Delta=1$、记录 $(re_1,e_2,-re_3)$、$q_j=r^{F_{j-1}}$；极限是合法中性 $\beta$ 制备 $(-e_3,e_1)$。同树／同码／同计数的中性和收缩世界可共享有限名字回复，仍给端点三点矛盾。这保留活跃 $d_0=1$，没有非法降低行列式。行5 $d_0>1$ 没中性，第69.2覆盖每个源及每个名字；这证明精确的“当且仅当”，其容差范围不能扩写为所有正 $E$。

**命题 70.5（每个有符号中性三标架的两叶局部源）。** 对任意中性 $(v_0,v_1,v_2)$，$\sigma=v_0\cdot(v_2\times v_1)=\pm1$。行5 $d_0\le1$ 取 $1/L<r<1$，$a=\sigma v_1/r,b=\sigma r v_2$；若 $\sigma=1$ 取 $t=\langle\beta,\alpha\rangle$，若 $\sigma=-1$ 取 $t=\langle\alpha,\beta\rangle$。准确记录为 $(v_0,rv_1,rv_2)$，$\Delta=1$，全部未来 $x_j=r^{F_j}v_{j\bmod3}$。

证明。中性三标架有 $v_2\times v_1=\sigma v_0,v_0\times v_2=\sigma v_1,v_1\times v_0=\sigma v_2$。$K=b\times a=\sigma v_0$；顺根树的前两更新值为 $K\times b=\sigma rv_1$ 及 $(K\times b)\times K=\sigma rv_2$。反转根在所有替换版本都乘 $-1$，给负定向的所需记录。两叶长 $1/r,r<L$，三读为 $1,r,r$，行列式1满足下界；递推给未来。它是 $N=2$ 的局部族，区别于上面的固定单叶 $\beta$、$(q_0,q_1,q_2)=(r,1,r)$。行3及行5 $d_0<1$ 还可同时缩放一个实际中性源的两叶：真实每时叶数 $N_j>0$ 给 $x_j(\lambda)=\lambda^{N_j}x_j(1)$，$\Delta$ 乘 $\lambda^4$ 最终仍合法；$N_j\to\infty$ 给逐源收缩。三种实际构造的用途和活跃边界不同。

## 71. 取得精度下界与可复用的首停反例

**定理 71.1（尖锐取得精度阶）。** 固定有理 $0<E\le1/2$。仅有普通三读名字和固定公共输入的全合法名字严格域取得程序，其请求精度和停止费用在来源间无统一界。沿第66.1族，某些合法名字迫使请求

$$b>\log_2\frac1{1-v_k}=k\log_2\varphi+O(1)=\log_2N_k+O(1).$$

第69.2、第68.2的最大请求精度在此族为 $O(k)$，故最坏合法名字的最大精度阶为 $\Theta(k)$。这是精度取得律；标准定宽 dyadic 回复的接收数值位有 $\Omega(k)$，不是任何格式的保留记忆下界。

证明。对来源 $s_k$，在所有 $2^{-b}\ge1-v_k$ 的请求上返回单位 $U$，更细处给准确 dyadic 近似；这是一个全精度合法名字。程序不能在任何有限单位回复前缀停止，因为该前缀兼容第70.3的三点实际纤维，误差须大于 $1/2$。在此合法名字上须有限停止，故先请求严格更细的精度。第66.1的对数间隙律给下界。其平方乘积真间隙 $1-v_k^4$ 与 $1-v_k$ 同阶；搜索余量证明及最终预算给固定 $E$、可选固定 $c_-$ 的 $O(k)$ 上界。第66.2有理族相同，行3的 $v\uparrow1$ 给无界结论。若存在统一步骤上限，单位路径的有限前缀总能由足够晚严格来源实现，到上限前不能可靠停止，矛盾。

定宽标准分子在单位尺度含 $b$ 位数量级字段，因此该格式的读入费用有下界；单位回复可用另一个压缩格式表示，保留字也可丢弃已读位，不能由请求下界推断格式无关最优记忆。原一次有限回复中，点态及统一停止都失败；点态与统一费用的区别发生在另外收费的严格域精化接口。

**命题 71.2（裸 $P<1$ 不给首停余量）。** 合法实际来源 $t=\alpha,p=(e_1,(127/128)e_2)$ 位于 $L=1,H=1,d_0=1/2$。给所有 $b\le6$ 单位回复，$b=7,8$ 给准确 dyadic 回复，其余精度按最近真值补全。这是同时误差至多 $2^{-b}$ 的合法名字。只以 $P<1$ 停止的线性轮询在 $b=8$ 首停，但其 $\kappa=(1+P)/2$ 不满足 $1-\kappa\ge g/4$。

证明。令 $v=127/128$，记录 $(e_1,ve_2,-ve_3)$，$\Delta=v^2\ge1/2$。$b\le6$ 的误差 $1/128\le2^{-b}$；$b=7$ 时 $\min(1,v^2+3/128)=1$。$b=8$ 时两个平方范数上包络为 $16321/16384$，故

$$g=1-v^4=\frac{8290815}{268435456},\qquad
1-\kappa=\frac{2060415}{536870912}<\frac g4.$$

这个反例是实际来源、全合法名字上的数学 falsifier；裸停止法仍可给点态证书，却不能据此继承同真间隙比较的成本结论。第69.2的严格余量测试直接在每次返回证明所需比较。

## 72. 分别收费的两条有限算术替代路线

**定理 72.1（有理径向裁剪）。** 假设单位真读、真有理 $q_1q_2\le\kappa<1$，以及额外真实 $0<c_-\le c$。令 $h=1-\kappa,A_0=10/c_-$；若

$$e\le\min\{1/2,h/8,E/[4(A_0+12/h)]\},$$

计算 $z_i=y_i/\max(1,|y_i|^2)$，再用未作标量裁剪的同一平方范数核 $P_j(z)$。全部未来误差至多 $2(A_0+12/h)e\le E/2$；舍入再加 $E/2$。这是有限有理除法路线，其条件和算术费用独立于第68节。

证明。径向投影 $P$ 到单位球非扩张：$(y-Py)\cdot(u-Py)\le0$ 对每个球内 $u$ 成立，交换两点相加给 $|Py-Pw|^2\le(y-w)\cdot(Py-Pw)$。故 $|Py_i-x_i|\le e$。若 $|y|>1$，$y/|y|^2$ 与 $Py$ 距离 $1-1/|y|\le|y|-1\le e$；否则不改。因此 $|z_i-x_i|\le d=2e$，$|z_i|\le1$。

真／报叉积差至多 $2d$。错号时，若 $q_0<2d$，锚差至多 $6d$；否则来源投影给

$$c_-q_0|w|\le d|w|+(q_0+d)2d\le4q_0d,$$

故第三锚差至多 $2d+8d/c_-\le A_0d$，前两锚也被此界控制。$d=0$ 直接用准确核。对真／报幅度 $u,v,u',v'\in[0,1]$，误差各至多 $d$，最大混合乘积至多 $\kappa+2d\le R=(1+\kappa)/2$。系数 $u^rv^s$ 的逐因子差在 $\min(r,s)\ge1$ 时至多 $(r+s)dR^{\min(r,s)-1}$。$j\ge5$ 的原幅度指数以 $a=F_{j-2}\ge2$ 满足 $\min(r,s)\ge a-1,r+s\le3a$，于是差至多 $3adR^{a-2}\le12d/h$；用 $R\ge1/2$ 及 $aR^{a-1}\le(1-R)^{-1}$。$j=3$ 系数1、$j=4$ 系数 $v^2$ 差至多 $2d$，同界覆盖。加锚差即结论。

取整数 $m\ge1$ 使 $2^{-m}\le\min(E/2,1/2)$，$n=\lceil1/h\rceil,T=mn$，$J$ 为最小 $F_{J-2}\ge T$。Bernoulli 给 $\kappa^n\le1/(1+nh)\le1/2$，包括 $\kappa=0$，故全尾输出零仍正确。$T=O((1+\log_+(1/E))/h),F_J=O(T+1)$；所需报告精度为 $O(1+\log_+(1/E)+\log(1/h)+\log(1/c_-))$。有理分母、除法、约分、准备工作与输出舍入均另计，不把此路线和主路线的较好坐标同时当免费收益。

**定理 72.2（通用未裁剪有限头）。** 单位真读、真有理 $q_2\le\kappa<1$ 下，无需 $c_-$。对 $0<E\le1$，选 $T\ge1$ 使 $\kappa^T\le E/2$、最小 $J\ge3$ 使 $F_{J-1}\ge T$，$D=\max(2,F_J)$。一次报告误差满足

$$e\le\min\{1/D,(E/108)^2,E/(12D)\}$$

时，头部未裁剪核加输出舍入 $E/2$、全部尾部零输出，满足全未来误差 $E$。

证明。头系数总幅度次数至多 $D$，真因子至多1、报告因子至多 $1+e$。逐因子替换的差至多 $D(1+e)^{D-1}e\le3De$，因为 $De\le1,(1+e)^D\le e^1<3$，后式由指数级数成立。报告系数至多3，真实锚至多1，第68节通用锚差至多 $9\sqrt e$。所以头误差至多 $27\sqrt e+3De\le E/2$；舍入给 $E$。$q_1\le1$ 给整个尾 $q_j\le\kappa^{F_{j-1}}\le E/2$。若 $J>3$，最小性给 $F_{J-2}<T,F_{J-1}<2T,F_J<3T$；因此 $D=O(T+1)$、最终精度 $O(1+\log(1/E)+\log D)$，所有零／错号／像外分支仍成立。若 $E>1$，可先选 $\epsilon\le\min(E,1)$ 运行此独立路线，主路线本身直接覆盖全部正 $E$。

一种独立名字发现法可按 $b=0,1,\ldots$ 对 $y_2$ 用整数平方比较取得有理范数上包络 $|y_2|\le v_b\le|y_2|+e_b$。设 $u_b=v_b+e_b$，只在 $u_b\le1-2e_b$ 停，返回 $\kappa=1-e_b$。真实 $q_2\le u_b\le q_2+3e_b$；$g_2=1-q_2>0$ 时 $e_b\le g_2/5$ 必停。首停不可能是 $b=0$；前一步失败给 $g_2<10e_b$，本步成功给 $2e_b\le g_2$，故 $g_2/10<1-\kappa\le g_2/2$。其调用数及接收位成本按自己的线性轮询收费，不能套用主路线倍增调用界。第67.3读前证书亦可接入此未裁剪核。这些备选保留独立证明及较宽无条件锚范围，不复制第52、54、58节已经发表的构造作为新增成果。

## 73. 完整有限算术程序及协议

以下为独立完整 Python 3 参考，使用标准整数、`fractions`、`json` 与 `sys`；安装解释器、库及全部代码的实际字节为收费固定程序成本。可将整块保存为 `reference.py`，调用 `python3 reference.py acquire` 或 `python3 reference.py query`。整数十进制转换无固定数字上限；增长的输入、输出及算术宽度仍实际收费。它保留第52、54、58节的不同已发表可选算术入口，取得 CLI 选择第68节平方范数裁剪核。

取得的首行是一个 JSON 配置，`source_id,frame_id` 为有限字符串；`E` 为正有理字符串。`mode` 为 `strict,size,stable,half,neutral,zero,rational,names`。`strict` 另给真实有理 `kappa`；`size` 给真实 `Nbar,d_lower`；`stable` 给真实 `hbar>=1,rho<1`；`half` 要求 `E>1/2`；`neutral,zero` 必须附真实中性／全零承诺；`names` 承诺捕获、响应不可变历史名字。配置所有承诺文本／选择／精度／身份属于付费完整字。可选 `c_lower` 为真实正有理条件证书。数学真域是合同前提，代码不从有限报告检验其物理真实性。

每个输出 `Read` 请求带来源、坐标系、版本、表示和所选精度。回复为一行 JSON，回显 `event,source_id,frame_id,version`；dyadic 另回显 `b` 和三个整数 `numerators`；rational 给三个准确有理 `coordinates`；name 给有版本绑定的认证 `handle`。`rho,Stop` 回复回显事件／身份并给 `ok:true`，承诺实际完成请求中的版本动作。日程严格为三读两更新 Stop，无 reset／校准。`NameRead` 是 Stop 后的额外收费历史服务，回显 `b,handles` 并给九整数，仍绑定三个已捕获版本；`CloseNames` 须确认，再发闭合 `Word`。捕获后的精化不读新的真实来源版本。

`Word` 含完整配置、所用有限报告／或准确有理三元组、日程、程序身份和来源／坐标系；零字可丢弃已经付费的瞬态回复。`name_precisions` 为另列的取得数值，若一同保留须另计其宽。Query 第一行可直接使用整个 Word 包装。其后每行一个规范二进制 $j\ge3$，换行是明确 END；禁止前导零、空白和非二进制字符，文件末未带 END 的最后令牌无效。解析器在有效／无效请求上都消费整条令牌，稳定／严格／库／零分支只保留饱和值及模3，准确有理分支实际构造整个 $j$。回复为 dyadic 三整数及 `fractional_bits`，或准确约分有理字符串；错误为固定有限 JSON 回复。

成功后查询只接闭合字，名称句柄已关闭，不连接供方。名字逐查询入口 `named_query` 则是另外保留持续名字的接口，并非 CLI 发出的闭合字。格式检查、身份回显、数值界和证书的有限算术蕴涵不验证供方真实性；伪造字、虚假证书和不响应供方在正确性承诺外。有效供方的各请求有限响应也没有统一物理时间保证。配置和 Word 首行被完整缓存，其输入缓冲按实际长度收费；后续请求逐字符流式消费，JSON 输出缓冲仍按实际长度收费。

```python
"""Finite-word arithmetic and declared-port reference. The CLI uses only the explicitly priced ports."""
from fractions import Fraction as Q

def isqrt(n):
    assert n >= 0
    if n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length()+1)//2)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid*mid <= n:
            lo = mid
        else:
            hi = mid
    return lo

def add(x, y):
    b = max(x[1], y[1])
    return ((x[0] << (b-x[1])) + (y[0] << (b-y[1])), b)

def neg(x):
    return (-x[0], x[1])

def mul(x, y):
    return (x[0]*y[0], x[1]+y[1])

def power(x, n):
    assert n >= 0
    z = (1, 0)
    while n:
        if n & 1:
            z = mul(z, x)
        n >>= 1
        if n:
            x = mul(x, x)
    return z

def dot(x, y):
    z = (0, 0)
    for a, b in zip(x, y):
        z = add(z, mul(a, b))
    return z

def cross(x, y):
    return tuple(add(mul(x[i], y[j]), neg(mul(x[j], y[i])))
                 for i, j in ((1,2), (2,0), (0,1)))

def scale(c, x):
    return tuple(mul(c, a) for a in x)

def anchors(nums, b):
    assert len(nums) == 9 and b >= 0
    y = tuple(tuple((nums[3*i+k], b) for k in range(3)) for i in range(3))
    w = cross(y[2], y[1])
    d = dot(y[0], w)[0]
    s = (d > 0) - (d < 0)
    return y[1], y[2], scale((s, 0), w)

def fib(n):
    assert n >= 0
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a+b
    return a

def kernel(nums, b, j):
    assert j >= 3
    y1, y2, z = anchors(nums, b)
    u, v = dot(y1,y1), dot(y2,y2)
    a, c = fib(j-2), fib(j-1)
    phase = j % 3
    if phase == 1:
        m, n, anchor = (a-1)//2, c//2, y1
        assert a % 2 == 1 and c % 2 == 0
    elif phase == 2:
        m, n, anchor = a//2, (c-1)//2, y2
        assert a % 2 == 0 and c % 2 == 1
    else:
        m, n, anchor = (a-1)//2, (c-1)//2, z
        assert a % 2 == 1 and c % 2 == 1
    return scale(mul(power(u,m),power(v,n)), anchor)

def round_num(x, p):
    """Nearest p-fractional-bit word; exact ties go away from zero."""
    n, b = x
    if b <= p:
        return n << (p-b)
    d = 1 << (b-p)
    r = (2*abs(n)+d)//(2*d)
    return r if n >= 0 else -r

def round_vec(x, p):
    return tuple(round_num(a,p) for a in x)


def output_precision(budget):
    assert budget > 0
    p, h = 0, Q(1)
    while h > budget:
        p, h = p+1, h/2
    return p

def producer_precision(e_star):
    # A paid finite sensor approximation must separately guarantee sigma <= e_star/2.
    return output_precision(e_star/2)

def setup_stable(hbar, rho, E, conditioned_c=None):
    hbar, rho, E = Q(hbar), Q(rho), Q(E)
    assert hbar >= 1 and 0 <= rho < 1 and E > 0
    R = (1+rho)/2
    P = 3*hbar*hbar + 3*hbar + 1
    Cs = 2*hbar+1 + 2*hbar*P
    if conditioned_c is None:
        K = Cs + R/(1-R)**2
        e_star = min(Q(1),(1-rho)/2,(E/(2*K))**2)
    else:
        c = Q(conditioned_c)
        assert 0 < c <= 1
        C = 4*(hbar*hbar+2*hbar+1)/c
        K = C + R/(1-R)**2
        e_star = min(Q(1),(1-rho)/2,E/(2*K))
    T, rpower = 0, Q(1)
    while rpower > E/2:
        T, rpower = T+1, rpower*R
    J, a, c = 3, 1, 2
    while c < T:  # c = F_J
        J, a, c = J+1, c, a+c
    return {'J':J, 'T':T, 'p':output_precision(E/2),
            'b':producer_precision(e_star), 'e_star':e_star, 'K':K, 'R':R}

def stable_query(nums, b, cfg, bits):
    j, _ = parse(bits, cfg['J'])
    if j == cfg['J']:
        return (0,0,0), cfg['p']
    return round_vec(kernel(nums,b,j),cfg['p']), cfg['p']

def setup_plateau(nums, b, tau):
    tau = Q(tau)
    assert tau > 0
    e_star = min(Q(1),(tau/31)**2)
    p = output_precision(tau/2)
    y1, y2, z = anchors(nums,b)
    u, v = dot(y1,y1), dot(y2,y2)
    bank = (scale((1,1),z), scale(mul((1,1),v),y1),
            scale(mul(mul((1,1),u),v),y2))
    return {'words':tuple(round_vec(x,p) for x in bank), 'p':p,
            'e_star':e_star, 'required_b':producer_precision(e_star)}

def plateau_query(cfg, bits):
    _, phase = parse(bits, 3)
    return cfg['words'][phase], cfg['p']

def norm_interval(vector, p):
    """Exact dyadic floor norm and upper enclosure of width 2**(-p)."""
    sq = dot(vector,vector)
    n, b = sq
    assert n >= 0 and 2*p >= b
    t = isqrt(n << (2*p-b))
    return (t,p), (t+1,p)

def setup_weighted(nums, b, norm_p, out_p):
    assert norm_p >= b and out_p >= 0
    y1, y2, z = anchors(nums,b)
    u = norm_interval(y1,norm_p)[0]
    v = norm_interval(y2,norm_p)[0]
    # Floor norms are nonnegative; clipping to 1 is an exact integer comparison.
    u = (min(u[0],1 << norm_p),norm_p)
    v = (min(v[0],1 << norm_p),norm_p)
    bank = (scale((1,1),z), scale(mul((1,1),v),y1),
            scale(mul((1,1),u),y2))
    return {'words':tuple(round_vec(x,out_p) for x in bank),'p':out_p,
            'norm_p':norm_p}

def setup_weighted_budget(nums, b, tau, conditioned_c=None):
    tau = Q(tau)
    assert tau > 0
    if conditioned_c is None:
        e_star = min(Q(1),tau/4,(tau/9)**2)
    else:
        c = Q(conditioned_c)
        assert 0 < c <= 1
        e_star = min(Q(1),tau/4,c*tau/16)
    cfg = setup_weighted(nums,b,max(b,output_precision(tau/4)),
                         output_precision(tau/2))
    cfg.update({'e_star':e_star,'required_b':producer_precision(e_star)})
    return cfg

def verify_conditioned_certificate(L_upper, d_lower, c_lower):
    L,d,c = Q(L_upper),Q(d_lower),Q(c_lower)
    # Arithmetic validation only; physical leaf/Gram promises are supplier owned.
    return L > 0 and d > 0 and 0 < c <= 1 and c*c*L**4 <= d

def verify_zero_certificate(L_upper, d_lower, H_upper):
    L,d,H = Q(L_upper),Q(d_lower),Q(H_upper)
    # Sufficient rational certificate, not an arbitrary-real regime classifier.
    return L > 1 and d >= L and H > 0 and H*H < d

def zero_query(bits):
    # Invoke only after a valid paid all-zero regime/source-class certificate.
    parse(bits,3)
    return (0,0,0),0

def setup_instance(kappa, E):
    kappa, E = Q(kappa), Q(E)
    assert 0 <= kappa < 1 and E > 0
    T, rpower = 0, Q(1)
    while rpower > E/2:
        T, rpower = T+1, rpower*kappa
    J = 3
    while fib(J-2) < T:
        J += 1
    N = fib(J)
    B = Q(2)**(N+1)*(9+N)
    e_star = min(Q(1),(E/(2*B))**2)
    return {'J':J,'p':output_precision(E/2),'b':producer_precision(e_star),
            'e_star':e_star,'N':N}

def finite_guard_round(raw_integer, b):
    # raw_integer is the paid (b+4)-fractional-bit coordinate approximation.
    return round_num((raw_integer,b+4),b)


def rational_kernel(replies, j):
    # Same squared-norm polynomial on the EXACT finite rational presentation class.
    assert len(replies) == 3 and all(len(v) == 3 for v in replies) and j >= 3
    y0,y1,y2 = (tuple(Q(c) for c in v) for v in replies)
    def dq(x,y):
        return sum((a*b for a,b in zip(x,y)),Q(0))
    w = tuple(y2[i]*y1[k]-y2[k]*y1[i] for i,k in ((1,2),(2,0),(0,1)))
    d = dq(y0,w)
    s = (d > 0)-(d < 0)
    z = tuple(s*c for c in w)
    u,v = dq(y1,y1),dq(y2,y2)
    a,c = fib(j-2),fib(j-1)
    if j % 3 == 1:
        m,n,anchor = (a-1)//2,c//2,y1
    elif j % 3 == 2:
        m,n,anchor = a//2,(c-1)//2,y2
    else:
        m,n,anchor = (a-1)//2,(c-1)//2,z
    coefficient = u**m*v**n
    return tuple(coefficient*x for x in anchor)

def setup_name_query(hbar, j, E):
    # ONLY the separately paid reusable Cauchy-name extension.
    hbar,E = Q(hbar),Q(E)
    assert hbar >= 1 and j >= 3 and E > 0
    R = hbar+1
    P = 3*hbar*hbar+3*hbar+1
    Cs = 2*hbar+1+2*hbar*P
    N = fib(j)
    B = R**(N+1)*(Cs+N)
    e_star = min(Q(1),(E/(2*B))**2)
    return {'j':j,'b':output_precision(e_star),'p':output_precision(E/2),
            'e_star':e_star,'N':N,'B':B}

def named_query(read_name, bits, E):
    # read_name(b) is a CHARGED finite access to the three already supplied names.
    # Its nine integers certify simultaneous vector error <= 2**(-b).
    # This callback does not exist in the original stopped finite-record interface.
    j = parse_unbounded(bits)
    coarse = read_name(0)
    assert len(coarse) == 9
    hbar = max(1,max(sum(abs(coarse[3*i+k]) for k in range(3))+1
                     for i in range(3)))
    cfg = setup_name_query(hbar,j,E)
    nums = read_name(cfg['b'])
    assert len(nums) == 9
    return round_vec(kernel(nums,cfg['b'],j),cfg['p']),cfg['p']
# Finite arithmetic core and JSON-lines acquisition protocol.
import json
import sys
# Exact finite rational and dyadic words have no uniform digit cap.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

def parse(bits, cap):
    if not isinstance(cap,int) or cap < 3:
        raise ValueError('bad cap')
    v, phase, seen, valid = 0, 0, False, True
    for digit in bits:
        if digit not in ('0','1') or (not seen and digit != '1'):
            valid = False
        seen = True
        if digit in ('0','1'):
            d = int(digit)
            v = min(cap,2*v+d)
            phase = (2*phase+d)%3
    if not valid or not seen or v < 3:
        raise ValueError('invalid query')
    return v,phase

def parse_unbounded(bits):
    v, seen, valid = 0, False, True
    for digit in bits:
        if digit not in ('0','1') or (not seen and digit != '1'):
            valid = False
        seen = True
        if digit in ('0','1'):
            v = 2*v+int(digit)
    if not valid or not seen or v < 3:
        raise ValueError('invalid query')
    return v

def qvalue(d):
    return Q(d[0],1 << d[1])

def dyadic(q):
    q=Q(q);d=q.denominator
    if d & (d-1):
        raise ValueError('not dyadic')
    return q.numerator,d.bit_length()-1

def clipped_kernel(nums,b,j):
    if j < 3:
        raise ValueError('bad j')
    y1,y2,z=anchors(nums,b)
    u=dot(y1,y1);v=dot(y2,y2)
    u=(min(u[0],1 << u[1]),u[1])
    v=(min(v[0],1 << v[1]),v[1])
    a,c=fib(j-2),fib(j-1)
    if j%3==1:
        m,n,anchor=(a-1)//2,c//2,y1
    elif j%3==2:
        m,n,anchor=a//2,(c-1)//2,y2
    else:
        m,n,anchor=(a-1)//2,(c-1)//2,z
    return scale(mul(power(u,m),power(v,n)),anchor)

def cutoff(kappa,E):
    kappa,E=Q(kappa),Q(E)
    if not 0 <= kappa < 1 or E <= 0:
        raise ValueError('bad cutoff parameters')
    T,rpower=0,Q(1)
    while rpower > E/2:
        T,rpower=T+1,rpower*kappa
    J,a,c=3,1,1 # a=F_(J-2), c=F_(J-1)
    while a < T:
        J,a,c=J+1,c,a+c
    return T,J

def setup_strict(kappa,E,c_lower=None):
    kappa,E=Q(kappa),Q(E)
    if not 0 <= kappa < 1 or E <= 0:
        raise ValueError('bad strict parameters')
    h=1-kappa*kappa
    if c_lower is None:
        K=9+18/h
        e_star=min(Q(1),h/12,(E/(2*K))**2)
    else:
        c=Q(c_lower)
        if not 0 < c <= 1:
            raise ValueError('bad conditioning certificate')
        K=max(Q(1),16/c)+18/h
        e_star=min(Q(1),h/12,E/(2*K))
    T,J=cutoff(kappa,E)
    return {'mode':'strict','kappa':kappa,'E':E,'K':K,'e_star':e_star,
            'b':output_precision(e_star),'p':output_precision(E/2),'T':T,'J':J,
            'c_lower':None if c_lower is None else Q(c_lower)}

def size_kappa(Nbar,d_lower):
    d=Q(d_lower)
    if not isinstance(Nbar,int) or isinstance(Nbar,bool) or Nbar < 1 or d <= 1:
        raise ValueError('bad paid size certificate')
    t=(d-1)/(2*d*Nbar)
    return 1-t/2

def check_nums(nums,b,hbar=1):
    if not isinstance(b,int) or isinstance(b,bool) or b < 0:
        raise ValueError('bad precision')
    hbar=Q(hbar)
    bound=(hbar.numerator*(1 << b)+hbar.denominator-1)//hbar.denominator+1
    if not isinstance(nums,list) or len(nums)!=9 or any(
       not isinstance(n,int) or isinstance(n,bool) or abs(n)>bound for n in nums):
        raise ValueError('bad nine-integer reply alphabet')
    return nums

def discover(read_name):
    b=1;history=[]
    while True:
        nums=check_nums(read_name(b),b)
        y1,y2,_=anchors(nums,b);e=Q(1,1 << b)
        q1=min(Q(1),qvalue(dot(y1,y1))+3*e)
        q2=min(Q(1),qvalue(dot(y2,y2))+3*e)
        P=q1*q2;history.append(b)
        if P+12*e < 1:
            return (1+P)/2,history
        b*=2

def acquire_names(read_name,E,c_lower=None):
    E=Q(E)
    if E > Q(1,2):
        cfg=setup_bank([0]*9,0,E,'half')
        nums=check_nums(read_name(cfg['b']),cfg['b'])
        cfg=setup_bank(nums,cfg['b'],E,'half')
        return {'cfg':cfg,'nums':nums,'b':cfg['b']},[cfg['b']]
    kappa,history=discover(read_name)
    cfg=setup_strict(kappa,E,c_lower)
    nums=check_nums(read_name(cfg['b']),cfg['b'])
    return {'cfg':cfg,'nums':nums,'b':cfg['b']},history+[cfg['b']]

def setup_bank(nums,b,E,mode,c_lower=None):
    E=Q(E)
    if E <= 0:
        raise ValueError('bad E')
    if mode=='half':
        tau=E-Q(1,2)
        if tau <= 0:
            raise ValueError('half needs E>1/2')
        e_star=min(Q(1),(tau/9)**2)
        p=output_precision(tau/2)
        factor=(1,1)
    elif mode=='neutral':
        e_star=min(Q(1),(E/18)**2)
        p=output_precision(E/2)
        factor=(1,0)
    else:
        raise ValueError('bad bank mode')
    y1,y2,z=anchors(nums,b)
    bank=(z,y1,y2)
    return {'mode':mode,'E':E,'e_star':e_star,'b':output_precision(e_star),
            'p':p,'J':3,'words':tuple(round_vec(scale(factor,v),p) for v in bank)}

def query_word(word,bits):
    cfg=word['cfg'];mode=cfg['mode']
    if mode=='rational':
        j=parse_unbounded(bits)
        return {'format':'rational','coordinates':[str(q) for q in rational_kernel(word['replies'],j)]}
    if mode=='zero':
        parse(bits,3)
        return {'format':'dyadic','numerators':[0,0,0],'fractional_bits':0}
    j,phase=parse(bits,cfg['J'])
    p=cfg['p']
    if mode in ('half','neutral','polynomial_bank','weighted_bank'):
        out=cfg['words'][phase]
    elif j==cfg['J']:
        out=(0,0,0)
    elif mode=='strict':
        out=round_vec(clipped_kernel(word['nums'],word['b'],j),p)
    elif mode=='stable':
        out=round_vec(kernel(word['nums'],word['b'],j),p)
    else:
        raise ValueError('unknown mode')
    return {'format':'dyadic','numerators':list(out),'fractional_bits':p}

def encode(obj):
    if isinstance(obj,Q):return str(obj)
    if isinstance(obj,dict):return {k:encode(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)):return [encode(v) for v in obj]
    return obj

def decode_word(word):
    cfg=word['cfg']
    for k in ('E','K','kappa','e_star','R','c_lower'):
        if k in cfg and cfg[k] is not None:cfg[k]=Q(cfg[k])
    if cfg['mode']=='rational':
        word['replies']=[[Q(c) for c in v] for v in word['replies']]
    return word

def send(obj):
    print(json.dumps(encode(obj),separators=(',',':')),flush=True)

def receive():
    line=sys.stdin.readline()
    if not line:raise ValueError('missing reply')
    return json.loads(line)

def exchange(req):
    send(req)
    reply=receive()
    if reply.get('event')!=req['event'] or reply.get('source_id')!=req['source_id'] or reply.get('frame_id')!=req['frame_id']:
        raise ValueError('reply identity mismatch')
    return reply

def acquire_protocol(config):
    # Source identity and physical truth are promised; finite checks enforce syntax only.
    mode=config['mode'];E=Q(config.get('E','1'))
    sid=config['source_id'];fid=config['frame_id']
    base={'source_id':sid,'frame_id':fid}
    cl=config.get('c_lower')
    if mode=='strict':cfg=setup_strict(config['kappa'],E,cl);hbar=Q(1)
    elif mode=='size':
        cfg=setup_strict(size_kappa(config['Nbar'],config['d_lower']),E,cl);hbar=Q(1)
    elif mode=='stable':
        hbar=Q(config['hbar']);cfg=setup_stable(hbar,Q(config['rho']),E,cl);cfg['mode']='stable';cfg['E']=E
    elif mode in ('half','neutral'):
        cfg=setup_bank([0]*9,0,E,mode,cl);hbar=Q(1)
    elif mode=='zero':cfg={'mode':'zero','J':3};hbar=Q(config.get('hbar','1'))
    elif mode=='rational':cfg={'mode':'rational'};hbar=None
    elif mode=='names':cfg=None;hbar=Q(1)
    else:raise ValueError('bad acquisition mode')
    nums=[];replies=[];handles=[]
    for i in range(3):
        req=dict(base,event='Read',version=i,representation=('name' if mode=='names' else 'rational' if mode=='rational' else 'dyadic'))
        if mode not in ('names','rational'):req['b']=cfg.get('b',0)
        rep=exchange(req)
        if rep.get('version')!=i:raise ValueError('read version mismatch')
        if mode=='names':handles.append(rep['handle'])
        elif mode=='rational':
            v=rep['coordinates']
            if len(v)!=3:raise ValueError('bad rational vector')
            replies.append([Q(c) for c in v])
        else:
            v=rep['numerators']
            if rep.get('b')!=req['b'] or len(v)!=3:raise ValueError('bad finite read')
            # Nine-word validation after acquisition also checks integers/bounds.
            nums.extend(v)
        if i<2:
            rep=exchange(dict(base,event='rho',from_version=i,to_version=i+1))
            if rep.get('ok') is not True:raise ValueError('update not acknowledged')
    rep=exchange(dict(base,event='Stop',version=2))
    if rep.get('ok') is not True:raise ValueError('Stop not acknowledged')
    history=[]
    if mode=='names':
        def read_name(b):
            rep=exchange(dict(base,event='NameRead',handles=handles,versions=[0,1,2],b=b))
            if rep.get('b')!=b or rep.get('handles')!=handles:raise ValueError('name binding mismatch')
            return rep['numerators']
        word,history=acquire_names(read_name,E,cl)
        rep=exchange(dict(base,event='CloseNames',handles=handles))
        if rep.get('ok') is not True:raise ValueError('names not closed')
    elif mode=='rational':word={'cfg':cfg,'replies':replies}
    elif mode=='zero':
        check_nums(nums,0,hbar);word={'cfg':cfg}
    else:
        b=cfg['b'];check_nums(nums,b,hbar)
        if mode in ('half','neutral'):cfg=setup_bank(nums,b,E,mode,cl)
        word={'cfg':cfg,'nums':nums,'b':b}
    # Complete word includes all supplied advice, format, identity and fixed program identity.
    word.update({'public_contract':config,'source_id':sid,'frame_id':fid,
                 'schedule':['Read0','rho','Read1','rho','Read2','Stop'],
                 'program_id':'rro-whole-future-reference-v1'})
    # History is accounting evidence, not hidden retained source advice.
    send({'event':'Word','word':word,'name_precisions':history})

def query_tokens(stream):
    # Explicit newline END; character iterator avoids buffering a whole query.
    while True:
        first=stream.read(1)
        if first=='':return
        ended=[False]
        def chars():
            ch=first
            while ch not in ('\n',''):
                yield ch
                ch=stream.read(1)
            ended[0]=(ch=='\n')
        yield chars(),ended

def main():
    if len(sys.argv)!=2 or sys.argv[1] not in ('acquire','query'):
        raise ValueError('invoke: python3 reference.py acquire|query')
    if sys.argv[1]=='acquire':acquire_protocol(receive());return
    first=receive()
    word=decode_word(first['word'] if 'word' in first else first)
    for chars,ended in query_tokens(sys.stdin):
        try:
            out=query_word(word,chars)
            if not ended[0]:raise ValueError('missing END')
            send({'event':'Reply',**out})
        except (ValueError,KeyError,TypeError,ZeroDivisionError):
            # parse has consumed every token character, including malformed input.
            send({'event':'Reply','error':'invalid query'})

if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,TypeError,ZeroDivisionError) as exc:
        send({'event':'Error','error':str(exc)})
        sys.exit(2)
```

## 74. 同一实现的完整资源、有限核验与边界

**资源合同 74.1。** 记 $C_{pub}$ 为所有实际保留公共有理数、配置、证书、格式及选择字段的位宽；$C_{prog}$ 为安装或复制的全部程序／解释器／整数有理库成本；$M_{id}$ 为实际源／坐标系／版本／动作／Stop元数据。单位域的九整数回复数值宽为 $O(9(b+1))$，$\bar H$ 域各坐标另加 $O(\log(1+\bar H))$。JSON 十进制数字及转义／标头按实际字符和编码位宽计。任意额外长身份和证书不能藏进“统一常数”。

主严格字保留 $O(9(b_f+1)+C_{pub}+C_{prog}+M_{id}+\log(J+1)+\log(p+1))$ 位，$C_{pub}$ 包括实际派生的 $K,e_*,\kappa$ 等。发现和最终精化分别支付第69.2的调用、精度、全部回复及算术，不只计保留字。半锚／中性字在这个具体程序同时保留九个原报告及九个已舍入库坐标，后一项 $O(9(p+1))$；即使另一实现可丢弃旧报告，本程序的重复保留也收费。零字丢弃已付费报告，保留证书、元数据与程序。准确有理字保留原九有理数的 $B$ 位以及全部公共／程序／身份宽。名字模式发出的闭合严格／粗字不再保留可调用名字能力，供方捕获、历史存储、精化回复、关闭服务均已付费；配置中的任何句柄文本仍计实际宽，关闭后不授查询权。

设置的 $T$ 次有理幂搜索中，分子分母宽为 $O((T+1)(C_{pub}+1))$；每次乘法、比较、约分都收费。采用含约分的保守立方位算术界，时间可取 $O((T+1)^4(C_{pub}+1)^3)$、暂存 $O((T+1)(C_{pub}+1))$，另外计实际 $b,p$ 二分和 $J$ 加法。严格／稳定头部令 $D=\max(2,F_J)$，安全工作宽

$$W=O(D(b_f+C_{pub}+1)+p+J).$$

固定多个 $W$ 位整数及 $O(J)$ 位 Fibonacci／幂指数足够。查询长度 $\lambda_q$、序列化输出长度 $\lambda_{out}$ 下，一个保守共同时间界为

$$O(\lambda_q\log(J+1)+J^2+\log(D+1)W^3+\lambda_{out}),\qquad
O(W+\log(J+1))\text{ 工作位},$$

另加已保留字和完整 Word 输入缓冲。纯 dyadic 乘法部分可用平方而非立方算术界。尾查询也消费整个令牌，输出三零，不跳过收费解析。三相位库支付自己的有限设置／舍入，再用 $O(\lambda_q+\lambda_{out})$ 时间和固定解析状态，JSON 输出缓冲单计。第72节径向除法和线性轮询的预算属于自己的路线；第54节加权库还付整数平方根，不能组合不同路线的最佳坐标当一个同时实现的免费向量。

准确有理查询的 $W_j=O(F_j(B+1)+j)$，时间保守为 $O(\lambda_q^2+j^2+jW_j^3+\lambda_{out})$，工作为 $O(W_j+\lambda_q)$，外加固定完整字；全 $j$ 无统一上限。持续名字逐查询还支付该次粗／精名字访问、回复、预算幂和供方工作，不能借用闭合字价格。固定容差／证书配置的稳定／库算法可有固定工作上界的有限状态实现族，准确有理增长是无界算术机；固定程序不意味着全来源、全配置、全输出宽度的单一有限控制器。

原来源费用也属于同一合同：准确原始三读、两次破坏性更新、固定共同制备／坐标系、传感精度发行及真证书／名字供应各实际收费。若另供字面树码，原组成 $(m,n)$ 的三个版本叶数为 $N_0=m+n,N_1=m+2n,N_2=2m+3n$，直接求三读要 $(N_0-1)+(N_1-1)+(N_2-1)=4m+6n-3$ 次叉积；字面替换扫描和输出 $O(N_0+N_1+N_2)$ 个节点，节点字段、深度栈、内部算术精度和输出宽度另计。这是第13、60节的准确复用，不授观察者树码／计数端口。供方发行、认证、访问、延迟和物理能量没有从观察者九字成本推出的统一界。

**证据与来源 74.2。** 数学结论由上述普通证明或精确引用的本卷证明承担；从第73节正文提取的完整程序执行得到以下有限读数。使用制备运输的准确有理检查覆盖102棵至多四叶有序树、6个制备、6732个准确查询；严格核9666个查询、半锚库6215个查询均满足其误差合同。检查另含 $j=5,\ldots,59$ 的指数范围、$j=3,4$ 例外、非正交像外回复、极小错号和零来源像外回复、$g=1$、$\kappa=0$、$E\ge2$ 及空头。八个完整有限供方协议分别覆盖名字严格、准确有理、较宽稳定、大小证书、名字粗平台、半锚、中性和零分支；名字关闭后只连接已输出字求值。准确增长的有限 $j=21$ 回复有5332个十进制字符，准确有理输入还包含5001字符整数，证实实现没有固定十进制数字帽。

不同检查路径直接对原字面树作 $\rho$ 替换并在固定同次制备求值：102棵树、7个制备、4284个准确有理未来查询，严格／零／大容差15744个查询；枚举每向量零或正负单坐标一格扰动，4116个同时合法报告查询通过通用／条件误差预算。三种有符号两叶／单叶见证分别核对；字面 $T_6$ 的13叶来源在两种准确有理制备上核对 $j=0,\ldots,8$；$k=6,12,18,24$ 的两个间隙常数作准确有理取样。四种包含非最近格点回复的合法名字检验实际返回余量；三个守护纤维向量及两个正负旋转最近真单元独立核对。120001字符合法查询及10002、10003字符无效查询均完整消费；交互式的严格名字、粗名字、严格证书和准确有理四种协议关闭取得服务后各核对9个查询，同时检验无效令牌和缺失 END。

这些是有限精确算术／有限模拟供方的执行结果。不同检查路径不等于独立数学评审，不验证任意实仪器、证书发行或物理名字服务；所有源、所有合法名字及无限未来的结论仍由普通证明承担。

成熟表示背景引用 Arno Pauly, *On the topological aspects of the theory of represented spaces*, [arXiv:1204.3763v3](https://arxiv.org/abs/1204.3763v3)，仅取表示／realizer及有限证据背景；不主张与未核对的期刊版本同一，也不把未经核对的中间印刷行用作证明前提。第70节有限圆柱和原来源纤维直接证明。经典叉积、原实际核、十制度、原 $H_*$、固定完整字平台端点、全实增长计数障碍、宽稳定域和既有位界均属复用。这里的源大小行列式律、归一化来源族、全时矩形系数估计和余量控制的取得是普通来源特定推导；不主张全球新颖性，也没有新增 kernel 验证。

通用有限视界伪度量可实例化状态为树与制备、更新为 $(t,p)\mapsto(\rho t,p)$、读出为 $E_p(t)$；第32.1节已给该对应。它本身没有全局输出界；另一个有界无限核结论不能应用到无界 $\mathbb R^3$ 增长。球面有限字纤维或概率有限前缀结果的全局界／乘积律前提也不能替代本卷实际确定性纤维证明。边界几何第47–48节及原子理论第425–426节处理不同来源／目标，不给这里原 R3 全未来任务免费端口。

**开放边界 74.3。** 保留的未决问题是最优保留字长／压缩、最优总运行时间／供方成本、平台中间完整风险曲线、任意实参数临界制度的有效分类，以及真实传感／证书／历史名字／共同坐标系的物理实现和价格。没有宣称空间、时钟和物理记忆装置已互恢复。付费服务的真实性与有限响应是条件前提，伪造输入或无响应不在承诺内；不会因此把原有限回复障碍改称已解决。理论与有限核验均不代替独立评审、准入检查或长期目标的完成。

## 追加锚（本行以下为增补区）

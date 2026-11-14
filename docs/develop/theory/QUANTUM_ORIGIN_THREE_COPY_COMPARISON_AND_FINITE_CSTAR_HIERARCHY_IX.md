# 三份原准备比较与全有限复 C* 张量层级 IX

> **卷际约定。** 本卷承接[第 VIII 卷][T132VIII]与[第 VII 卷][T132VII]。
> 第 132 章固定 VIII128.1 的同一个源及补全，不另选高阶锥。
> 本卷只增不减；修订与增补续于文末追加锚之后，保留既有条目、编号与引用。

## 132. 同源三角形的固定门户、原矩阵锥与秩一切片排除

### 132.A 完整原域及一个固定的规范族

**定义 132.1（同一个原三角形与规范门户）。** 原来源版本固定为提交
`76227a176b079ca94637adca93f6010bb0962a79`。
固定其中 [VIII123.1—123.2、125.1、128.1][T132PinnedVIII]
的同一个 $\mathcal D,S,\mathcal K,E$、原实际标签与计算相位基，始终取

$$
B_{\mathcal D}(w)\subseteq E(w)=E(w)^\vee
 \subseteq A_{\mathcal D}(w)=B_{\mathcal D}(w)^\vee,
\qquad b_w(H,L)=\operatorname{Tr}(H^TL).
\tag{132.1}
$$

载体是复 Hermitian 空间的真正实张量积；$T$ 是固定基中的全转置。
不要求 $E$ 或 $\mathcal K$ 在全转置或部分转置下不变。
保留整个原输入锥

$$
x\in E(A_1A_2A_3),\quad y\in E(A_4A_5A_6),\quad
z\in E(A_7A_8A_9),
\tag{132.2}
$$

九个实际位置均为 qutrit，实际标签可以重复。输出与帽严格采用 VIII(128.3)：
帽矩阵为 $R,S,T\in M_3(\mathbb C)$，未匹配资源为
$X\in\mathcal K_{k,3}$、$Y\in\mathcal K_{\ell,3}$、$W\in\mathcal K_{m,3}$。
三个量子尺寸各自任意正有限，无统一上界。记这个原输出为
$M_{R,S,T;X,Y,W}(x,y,z)$。最终仍测试全部联合 $F\succeq0$，读数为
$\operatorname{Tr}(F^TM)$，不把输入假定为普通 PSD。

取原标准基中的实嵌入

$$
J:\mathbb C^2\longrightarrow\mathbb C^3,
\quad J|r\rangle=|r\rangle\ (r=0,1),\qquad
\chi=|0,0\rangle+|1,1\rangle,\qquad X_0=\chi\chi^*.
\tag{132.3}
$$

$X_0\in\mathrm{SN}_2(2,3)\subseteq\mathcal K_{2,3}=\mathrm{PSD}_6$。
定义唯一的规范输出族

$$
M^0_{Y,W}(x,y,z)=M_{I_3,I_3,I_3;X_0,Y,W}(x,y,z).
\tag{132.4}
$$

三个规范帽仍秩三。秩二在此指未匹配门户，不能与 VIII127.6 的低秩跨输入帽混同。
一体实际 CP、所有量子 CP、分别支付的秩二双向接口、全部旁观扩张与原置换
均按 VIII123.2 使用；不增加多实际腿集体 CP，也不给任意 $E$ 元素制备箭头。

### 132.B 全部帽与一个未匹配门户的精确消去

**定理 132.2（完整 $k=2$ 与一个 $\mathrm{SN}_2$ 门户的同源等价）。**
对定义132.1的每个固定原源及同一个 $E$，下列三个全称命题等价：

1. VIII128.1 的全部 $k=2$ 三角形输出 PSD，$X$ 遍历整个原 $\mathcal K_{2,3}$，
   其余两个量子尺寸、原资源、整个三输入锥及复秩三帽全部保留。
2. (132.4) 的全部规范输出 PSD，$x,y,z$ 仍遍历各自整个原锥，
   $Y\in\mathcal K_{\ell,3}$、$W\in\mathcal K_{m,3}$，$\ell,m$ 任意有限无界。
3. VIII128.1 的全部有限尺寸三角形，只要至少一个未匹配门户属于其原
   $\mathrm{SN}_2$ 子锥，就有整个联合输出 PSD；另外两个门户不受此限制。

这些等价也允许奇异或零帽。它们不宣称三个命题已经成立。

**证明。** 先证明逐元恒等式，所有矩阵均允许复系数。对
$A:\mathbb C^2\to\mathbb C^k$、$D\in M_3(\mathbb C)$，令
$\xi=(A\otimes D)\chi$。原门户的数值作用是

$$
\Phi_X(H)_{ij}=\sum_{c,c'}X_{ic,jc'}H_{cc'}.
\tag{132.5}
$$

由于 $\xi_{ic}=\sum_{r=0}^1A_{ir}D_{cr}$，直接代入得到

$$
\Phi_{\xi\xi^*}(H)
 =A\Phi_{X_0}(D^TH\overline D)A^*.
\tag{132.6}
$$

这里 $D^TH\overline D=\operatorname{Ad}_{D^T}(H)$，不是
$D^*HD$。此恒等式对全部矩阵 $H$ 成立，故可保留任意旁观及所有非对角块。
帽的系数同样给

$$
\begin{aligned}
x_r&=(\operatorname{Ad}_{R^T}\otimes\operatorname{Ad}_{S^T}
                  \otimes\operatorname{Ad}_{D_r^T})(x),\\
y'&=(\mathrm{id}\otimes\operatorname{Ad}_{T^T}\otimes\mathrm{id})(y),
\qquad U_r=A_r\otimes I_\ell\otimes I_m.
\end{aligned}
\tag{132.7}
$$

这些是三个或一个分别合法的一体实际 CP 的复合，因而
$x_r\in E(A_1A_2A_3)$、$y'\in E(A_4A_5A_6)$；实际类型和位置没有改变。
例如第一帽的收缩使用
$\sum_a(R^T)_{da}x_{abc,\ldots}=\sum_aR_{ad}x_{abc,\ldots}$，
其 bra 系数是相应复共轭；第二、第三帽逐项相同。
因此只要 $X=\sum_r\xi_r\xi_r^*$、$\xi_r=(A_r\otimes D_r)\chi$，
原 VIII(128.3) 就给精确的整个输出恒等式

$$
\boxed{
M_{R,S,T;X,Y,W}(x,y,z)
 =\sum_r U_r M^0_{Y,W}(x_r,y',z)U_r^*.}
\tag{132.8}
$$

不存在被丢掉的交叉相位、输入转置或量子端口。全转置只仍在原最终配对中。

任意 $\xi\in\mathbb C^k\otimes\mathbb C^3$ 的 Schmidt 秩至多二，
当且仅当其系数矩阵可分解为 $AB^T$，其中 $A$ 为 $k\times2$、$B$ 为 $3\times2$。
把 $B$ 添上零第三列即得所需 $D$。在固定有限维度，$\mathrm{SN}_2$ 中每个元素
有这种 dyad 的有限非负和：单位 Schmidt 秩至多二向量组成紧集，
其 dyad 的紧凸包由有限维凸包定理给有限表示；正迹归一后再乘回原迹。
零元素取空和。每个和项本身都在同一原 $\mathcal K$ 中。
所以(132.8)证明命题2蕴含第一个门户属于 $\mathrm{SN}_2$ 的全部命题3；
其它门户位置由原输入、实际腿与量子输出的置换运输。
若恢复字面位置需要恢复不同的 qutrit 扇区标签，使用其间以恒等矩阵实现的一体实际 CP
及其逆；它们都是同一源中的保迹箭头，保持固定基，不另选补全。
未使用任意两个 $E$ 元素的乘积成员关系。

当 $k=2$ 时，整个原资源锥恰为 $\mathrm{PSD}_6$。
任意有限谱分解 $X=\sum_r\xi_r\xi_r^*$ 可在每项取 $A_r=I_2$，
并令 $(D_r)_{ci}=(\xi_r)_{ic}$，$i=0,1$，第三列取零。
于是还得到比正性传递更强的精确等式

$$
M_{R,S,T;X,Y,W}(x,y,z)
 =M^0_{Y,W}\left(\sum_rx_r,y',z\right),\qquad
\sum_rx_r\in E(A_1A_2A_3).
\tag{132.9}
$$

这一步把全部 $k=2$ 门户连同帽消去，没有留下对谱分量的输入锥扩大。
命题1蕴含2，因为规范族是合法子族；命题3蕴含1，因为
$\mathcal K_{2,3}=\mathrm{PSD}_6=\mathrm{SN}_2(2,3)$。等价得证。

若(132.8)左侧在 $h$ 上为负，则有限和中至少一项在
$U_r^*h$ 上为负，且这个向量非零。因此一个原负见证必传到同一原源的规范负见证。
反向直接取规范数据。$k=2$ 时(132.9)甚至保持相同的输出矩阵及负向量。
所有步骤不取逆、不除以本征值，故包括奇异、零和重复项。∎

### 132.C 混合矩阵锥的双向原 retract 与确切的待证扩张

**定理 132.3（规范族的源完全正性与第二层精确剩余）。** 固定
$y,z,Y,W$ 为132.1的任意合法剩余数据。只作坐标识别，令

$$
\begin{aligned}
\mathscr B_n&=B_{\mathcal D}(Q_nA_1A_2),&
\mathscr C_n&=E(Q_nA_1A_2),\\
\Lambda(H)_{\alpha u,\beta v}
 &=\sum_{\substack{a,b,e,f,t\\a',b',e',f',t'}}
 H_{ab,a'b'}\,y_{aef,a'e'f'}\,z_{bet,b'e't'}
 Y_{\alpha f,\beta f'}W_{ut,vt'}.
\end{aligned}
\tag{132.10}
$$

$\Lambda:M_9(\mathbb C)\to M_{\ell m}(\mathbb C)$ 由此复线性延拓，保持伴随。
它是原收缩的数值线性映射，不据其定义新增源箭头。
矩阵载体 $M_n(M_9)$ 的识别不把 $A_1A_2$ 变为免费量子对象。
有下列三个结论。

1. 对每个 $n\ge1$，
   $(\mathrm{id}_n\otimes\Lambda)(\mathscr B_n)\subseteq\mathrm{PSD}_{n\ell m}$。
   特别地，$\mathscr B_1=\mathscr C_1=\mathrm{PSD}_9$，所以 $\Lambda$ 普通正。
2. 对固定的 $y,z,Y,W$，全部 $x$ 的规范输出 PSD，恰等价于

$$
(\mathrm{id}_2\otimes\Lambda)(\mathscr C_2)
 \subseteq\mathrm{PSD}_{2\ell m}.
\tag{132.11}
$$

   再对剩余数据取全称即得到整个规范族。规范负见证与一个
   $H\in\mathscr C_2\setminus\mathscr B_2$ 的
   $(\mathrm{id}_2\otimes\Lambda)(H)$ 负见证双向传递。
3. $\mathscr B_2=\mathscr C_2$ 是(132.11)的充分条件。
   如果把此处特定的 $\Lambda$ 族扩大到所有从 $\{\mathscr B_n\}$ 完全正的线性映射，
   那么要求第二层在 $\mathscr C_2$ 上正就等价于这个锥等式；
   输出只取 $M_2$ 的映射已经足够。这不是说这些映射都能由原三角形实现。

**证明。** 将 $Q_n$ 单独放在最前，量子矩形 CP 保证
$\{\mathscr B_n\}$、$\{\mathscr C_n\}$ 都在矩阵合同下相容。
例如 $G:\mathbb C^m\to\mathbb C^n$ 给
$(G^*\otimes I_9)\mathscr B_n(G\otimes I_9)\subseteq\mathscr B_m$，
$\mathscr C$ 同理。这里的“完全正”只指逐层保持这些指定锥，
采用 Paulsen—Todorov—Tomforde [定义2.3及2.4后的映射定义][T132PTT]；
不把它偷换为普通矩阵代数的 PSD 层。

对 $H\in\mathscr B_n$ 的有限源态和，把该源态插入(132.10)，
其余帽、$Y,W$ 与量子旁观组成一个只有 $y,z$ 两个任意 $E$ 输入的原源箭头，
目标为 $Q_nQ_\ell Q_m$。直接复用 VIII127.2，目标为 PSD。
锥和与有限维连续性扩展到全部闭源态锥，证明第1项，保留源图内任意高中间次数。
$n=1$ 的等式正是 VIII127.2 的无参考两实际腿锚。
这个论证既不要求 $y\otimes z\in E$，也不把 $H$ 的非 PSD 性当作负输出。

令 $q$ 为在 $A_3$ 上分别已付的 $\operatorname{Ad}_{J^*}$，再把量子输出放在最前；
令 $j$ 为反向 $\operatorname{Ad}_J$，再恢复原位置顺序。
VIII123.2(v)给这两条箭头及其全部旁观扩张，数值上 $qj=\mathrm{id}$。
所以有真正的全锥等式

$$
q\bigl(E(A_1A_2A_3)\bigr)=\mathscr C_2,
\quad j(\mathscr C_2)\subseteq E(A_1A_2A_3),
\quad qj(H)=H.
\tag{132.12}
$$

这里两个包含分别由两条源箭头给出，满射由 $qj=\mathrm{id}$ 给出。
不使用任意 $E$ 元素的源制备或一个未经支付的伴随。
逐指标有 $(q x)_{iab,ja'b'}=x_{abi,a'b'j}$，其中 $i,j=0,1$。
由(132.3)的实系数，规范输出精确为

$$
M^0_{Y,W}(x,y,z)=(\mathrm{id}_2\otimes\Lambda)(q x).
\tag{132.13}
$$

(132.12)同时给必要性和充分性，并把任意混合锥负见证经 $j$ 送回合法原输入。
第1项又排除 $H\in\mathscr B_2$ 的负值，证明第2项。

为说明第3项的精确强度，在 $\mathscr B_2\subsetneq\mathscr C_2$ 时取
$H\in\mathscr C_2\setminus\mathscr B_2$。
有限维闭凸锥分离给实线性 $f$，使 $f(\mathscr B_2)\ge0$ 且 $f(H)<0$。
将 $f$ 唯一复线性延拓到全部矩阵，并用 $2\times2$ 矩阵单位定义

$$
\phi(V)_{ij}=f(E_{ij}\otimes V),\qquad i,j=0,1.
\tag{132.14}
$$

因为 $f(Z^*)=\overline{f(Z)}$，$\phi$ 保持伴随。
任取 $U=[U_{ab}]\in\mathscr B_n$、$G\in M_{n,2}(\mathbb C)$，
令 $v_G=\sum_{a,i}G_{ai}|a,i\rangle$，则

$$
\begin{aligned}
v_G^*(\mathrm{id}_n\otimes\phi)(U)v_G
 &=f\left(\sum_{i,j}E_{ij}\otimes
       \sum_{a,b}\overline{G_{ai}}U_{ab}G_{bj}\right)\\
 &=f\bigl((G^*\otimes I_9)U(G\otimes I_9)\bigr)\ge0.
\end{aligned}
\tag{132.15}
$$

最后的成员关系正是源的量子合同相容性。因此 $\phi$ 从源矩阵锥完全正。
但 $\Omega_2=|0,0\rangle+|1,1\rangle$ 满足

$$
\Omega_2^*(\mathrm{id}_2\otimes\phi)(H)\Omega_2
 =\sum_{a,b}f(E_{ab}\otimes H_{ab})=f(H)<0.
\tag{132.16}
$$

这证明锥等式的必要性；充分性由源完全正性立即得到。
此分离是常用矩阵锥对偶的直接应用：要求所有源完全正映射自动通过
第二层扩张，准确等价于上述更强锥等式；特定 $\Lambda$ 族只需(132.11)。
这里既未证明 $\mathscr B_2\ne\mathscr C_2$，也未把分离映射 $\phi$ 实现成一个合法三角形。∎

### 132.D 秩一条件联合输出的完整相干排除

**定理 132.4（一个秩至多一切片支付整个 $k=2$ 输出）。**
对 VIII128.1 的任意合法 $k=2$ 数据，包括全部复帽、奇异资源、
任意有限无界 $\ell,m$ 和三个整个原 $E_3$ 输入，若存在非零
$q\in\mathbb C^2$，使

$$
A_q=(q^*\otimes I_{\ell m})M(q\otimes I_{\ell m})
\quad\text{满足}\quad\operatorname{rank}A_q\le1,
\tag{132.17}
$$

则 $M\succeq0$，从而每个联合 PSD 效应均有非负原读数。
因此每个原负三角形必满足
$\operatorname{rank}A_q\ge2$ 对所有 $q\ne0$ 成立。
这里是一个条件联合输出的秩，不要求任何输入 PSD、任何门户可分或任何单端口边缘纯。

**证明。** 直接复用 VIII128.2，$M$ 在三个量子单端口对其余端口的二分上都块正。
令 $L=\mathbb C^\ell$、$R=\mathbb C^m$。
在第一个纯量子因子作酉换基并正缩放 $q$，可令(132.17)为

$$
M=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},\qquad
A,C\succeq0,\qquad \operatorname{rank}A\le1.
\tag{132.18}
$$

这是输出矩阵上的普通量子坐标变换，不是对原实际锥取相位商。
第一个二分上的块正性给，对每个 $w\in L\otimes R$，

$$
|w^*Bw|^2\le(w^*Aw)(w^*Cw).
\tag{132.19}
$$

若 $A=0$，则 $w^*Bw=0$ 对全部复 $w$ 成立；复极化给 $B=0$，遂 $M\succeq0$。
下设 $A=aa^*$，$a\ne0$。对每个 $p\in L$，第二个二分的块正性说明
在 $L$ 上压缩后的整个 $\mathbb C^2\otimes R$ 矩阵 PSD。
记 $a_p=(p^*\otimes I_R)a$、$B_p=(p^*\otimes I_R)B(p\otimes I_R)$。
PSD 块矩阵的核条件于是给

$$
\operatorname{ran}B_p\subseteq\mathbb C a_p,
\qquad a_p=0\Longrightarrow B_p=0.
\tag{132.20}
$$

核条件可直接验证：若 $s\in\ker(a_pa_p^*)$，在向量 $(s,tv)$ 上取二次型，
任意小复 $t$ 的线性项必须为零，故 $s^*B_pv=0$ 对全部 $v$ 成立。
它不需要可逆对角块。

先处理 $a$ 的 $L\mid R$ Schmidt 秩至少二的情形。
取 $L$ 的正交基，写 $a=\sum_i e_i\otimes a_i$、$B=[B_{ij}]$。
固定 $v\in R$，(132.20)蕴含

$$
\left(\sum_i z_i a_i\right)\wedge
 \left(\sum_{i,j}z_i\overline z_j B_{ij}v\right)=0
\quad(z\in\mathbb C^\ell).
\tag{132.21}
$$

每个外积坐标都是 $z,\overline z$ 的多项式。用
$z_i=x_i+iy_i$、$\overline z_i=x_i-iy_i$ 是可逆的复线性变量替换，
恒等为零意味着每个 $z$、$\overline z$ 单项式系数为零。
按 $\overline z_j$ 分组，得到对每个固定 $j,v$，

$$
\left(\sum_i z_i a_i\right)\wedge
 \left(\sum_i z_i B_{ij}v\right)=0
\quad\text{对全部 }z.
\tag{132.22}
$$

此处需要而且具备下述两映射事实。若线性映射 $F,G$ 满足
$Fz\wedge Gz=0$ 对全部 $z$ 成立且 $\operatorname{rank}F\ge2$，则 $G=\lambda F$。
证明如下：若 $z\in\ker F$，选 $z_1,z_2$ 使 $Fz_1,Fz_2$ 独立，
把 $z+tz_i$ 代入外积恒等式可知 $Gz$ 同时在两条独立像线中，故为零。
于是 $G$ 经 $F$ 的像因子化为线性映射，该映射保持每条像射线；
对任意两个独立向量及其和比较系数，全部比例相同。
这个事实不适用于秩一 $F$；该例外在下段单独处理。

将此事实应用于 $Fz=\sum_i z_i a_i$ 和
$Gz=\sum_i z_i B_{ij}v$，得到
$B_{ij}v=a_i\lambda_j(v)$。
选一个非零 $a_i$，唯一性及 $B_{ij}$ 的线性性说明 $\lambda_j$ 是线性泛函。
故存在 $r\in L\otimes R$ 使

$$
B=ar^*.
\tag{132.23}
$$

若 $a$ 的 Schmidt 秩为一，写 $a=u\otimes v$，两因子非零。
(132.20)给 $\operatorname{ran}B_p\subseteq\mathbb Cv$ 对全部 $p$ 成立。
投影到 $v^\perp$ 后，$\sum_{i,j}\overline p_i p_j B_{ij}$ 恒为零；
复极化给每个投影后的块为零，故
$\operatorname{ran}B\subseteq L\otimes\mathbb Cv$。
第三个二分的相同压缩与核条件则给
$\operatorname{ran}B\subseteq\mathbb Cu\otimes R$。
两空间交为 $\mathbb C(u\otimes v)$，再次得到(132.23)。
这一步保留了共同一维像的例外，未由局部线性相关错误推出全局比例。

把(132.23)代入(132.19)。在 $w^*a\ne0$ 时约去其模平方，得
$|r^*w|^2\le w^*Cw$。这些 $w$ 稠密，连续性将不等式延到全部 $w$，
所以 $C-rr^*\succeq0$。最终得到显式证书

$$
\boxed{
M=
 \begin{pmatrix}a\\r\end{pmatrix}
 \begin{pmatrix}a\\r\end{pmatrix}^{\!*}
 +|1\rangle\langle1|\otimes(C-rr^*)\succeq0.}
\tag{132.24}
$$

回到原量子基即得结论。任意非零 $q$ 的原生效应代表为
$G=\overline q\,\overline q^*$，VIII(128.5)恰给(132.17)，
故没有遗漏该压缩中的最终转置。$L$ 或 $R$ 一维、零切片和奇异 $C$ 都已包含。
这是一条关于原三角形输出的附加排除，不证明存在此前未覆盖的合法元组实现该秩条件。∎

### 132.E 原预算、源成员及负见证的边界

**命题 132.5（规范化保持的原标量与 proper 缩放）。**
(132.8)—(132.13)均为未归一张量的精确等式。
它们可与原 proper 缩放一起使用，但不声称确定性滤波或相同条件成功率。
具体地，对(132.7)内每个矩阵 $L$ 取
$a_L=\max\{1,\|L\|_{\rm op}\}$，用 $L/a_L$ 代替 $L$。
再令 $\widehat A_r=A_r/a_{A_r}$，所得滤波输入记为 $\widehat x_r,\widehat y$。
则原输出恰为

$$
M=\sum_r c_r(\widehat A_r\otimes I_{\ell m})
 M^0_{Y,W}(\widehat x_r,\widehat y,z)
 (\widehat A_r\otimes I_{\ell m})^*,\qquad
c_r=(a_{R^T}a_{S^T}a_{D_r^T}a_{T^T}a_{A_r})^2.
\tag{132.25}
$$

每个滤波不增原迹，全部因子 $c_r$ 明列而不充作概率权重。
对任何一个非零规范项，令三输入迹为 $t_x,t_y,t_z>0$、
两剩余资源迹为 $t_Y,t_W>0$，取 $s\ge\|F\|_{\rm op}$ 且 $s>0$。
在输入和资源各自除以其迹、$X_0$ 除以二、三帽各为原 $\beta_3/3$、
最终量子效应为 $F/s$ 时，规范标量严格等于

$$
\frac{\operatorname{Tr}(F^TM^0_{Y,W}(x,y,z))}
 {54\,s\,t_xt_yt_zt_Yt_W}.
\tag{132.26}
$$

**证明。** 每个 $L/a_L$ 是收缩 Kraus 矩阵，其迹亏损效应
$I-(L/a_L)^*(L/a_L)\succeq0$，按 VIII123.2(v)在所有原旁观下正。
因而原滤波不增迹；等式(132.25)仅将所有被除的正平方乘回。
对量子合同 $\widehat A_r$，普通 CP-TNI 预算来自
$I_2-\widehat A_r^*\widehat A_r\succeq0$。
即使尚未证明规范 $M^0$ 为 PSD，其迹亏损
$\operatorname{Tr}\bigl[((I_2-\widehat A_r^*\widehat A_r)\otimes I_{\ell m})M^0\bigr]$
仍由 VIII128.2 第一量子切口的块正性非负：将 $I_{\ell m}$ 展成正交 dyad 后逐项测试即可。
$q=\operatorname{Ad}_{J^*}$ 也是不增迹的原压缩，$j=\operatorname{Ad}_J$ 保迹，
像外的第三坐标被真正送零。$X_0$ 的迹为二，恒等 qutrit 帽的原 proper 系数为三，
所以(132.26)的因子为 $2\cdot3^3=54$；其余因子来自各输入与量子效应的正缩放。
这个计算不使任意 $E$ 输入获得实际制备资格，也不把 $c_r$ 的和归一化。
若原网络已经给定 proper 前因子，应把它乘在(132.8)或(132.25)的同一个标量上；
不得丢掉该前因子而把规范事件的成功率冒充原成功率。
零数据直接使用未归一等式给零，不条件化。

最终若 $h^*Mh<0$，合法原生 PSD 测试是
$F=\overline h\,\overline h^*$，因而 $\operatorname{Tr}(F^TM)=h^*Mh$；
取正 $s\ge\|h\|^2$ 即给 proper 量子效应且仍严格负。
在(132.8)的一项上，原效应拉回为 $U_r^TF\overline{U_r}\succeq0$，
与负向量 $U_r^*h$ 相符。这只传递已有且成员已认证的负值，不构造负值。
特别地，VIII128.4的非 PSD 混合张量本来在 $\mathscr B_2$ 内，
由132.3第1项不能产生这种负输出；不能把其负普通投影当作原混合类型的效应。∎

### 132.F 数学来源及完整未决义务

**约定 132.6（来源与结论范围）。** 132.2的承重内容是同一个原源上的
全部帽消去、固定门户等价及一个 $\mathrm{SN}_2$ 门户的全尺寸传递；
132.3的承重内容是原混合锥上的双向满射及特定收缩族的精确剩余；
132.4把范围定位给出的正分解用于整个原输出。
这些是固定源条件下的仓内推导（repo-derived），不主张外部优先权或文献原创性。
有限谱分解、Schmidt 分解、闭凸锥分离和 PSD 块核条件均为既有工具，
只在这些源应用的证明内使用，不另计作新结果。

矩阵序与完全正性的定义按 Paulsen—Todorov—Tomforde，
[*Operator System Structures on Ordered Spaces*, arXiv:0904.3783v2][T132PTT]，
定义2.3—2.4。其定理3.22(iii)关于 $\operatorname{OMAX}$ 的普遍性质
需要指定该矩阵序；它不把这里的 $\mathscr C_n$ 识别为
普通 $\mathrm{PSD}_{9n}$ 或 $\mathscr B_n$。
本章的分离计算(132.14)—(132.16)直接固定全部指标，不借那个普遍性质扩大结论。

Choi 与全转置双线性配对采用 Kye，
[*Compositions and tensor products of linear maps between matrix algebras*,
arXiv:2204.02516v2][T132Kye]，§2式(2)：常规 Choi 矩阵为
$C_\phi=\sum_{a,b}E_{ab}\otimes\phi(E_{ab})$。
因此(132.5)的 Choi 矩阵只是 $X$ 的两个因子换序，没有额外输入转置。
此字典不把任意原门户变成普通 CP 映射，也不提供原 $E$ 的产品闭包。

局部线性相关与全局比例的区别采用 Brešar—Klep，
[*A Local-global principle for linear dependence of noncommutative polynomials*,
arXiv:1103.1884v1][T132BK]，§2.4所指出的共同一维像例外。
132.4的证明给出所需的两映射论证，并另用第三二分处理该例外；
不把其一般局部相关定理误作无条件比例结论。

**未决问题 132.7（保留全称原义务）。** 是否对(132.10)的每个原收缩族
与整个 $\mathscr C_2$ 都成立(132.11)，仍未证明也未被原成员负见证反驳。
等价地，仍须对所有规范数据证明 VIII(128.28)的不同向量相干不等式，
包括零对角读数的核条件；132.4只排除了存在秩至多一条件联合输出的情形。
在其余分支，所有非零 $q$ 的条件联合输出秩至少二。
抽象分离映射没有被实现为原合法 $y,z,Y,W$，源饱和也未取得。

VIII125.8的整个 R3/R4、高中间次数、三个非 $\mathrm{SN}_2$ 门户的三角形、
其余循环、同源六份存在及全部有限 $N$ 的原 min/max 产品律均继续保留。
目标仍是原 allN 的 $\mathsf{Fusion}_3/t=1$，或保留全部原合同而有统一严格间隙的合法 allN 模型；
本章的等价归约与输出排除不完成该目标。

[EXCLUSION XI142.2及142.4][T132XI]的完整静态表示依赖 EB3、Conn、源接口及固定根纯芽
$\mathsf G(o)$；[XI143.4—143.5][T132XI]的表示依赖 EB3、Conn及统一正可读直径差额
$\mathsf U$。这些条件结论均不把当前任意三实际腿或混合输入识别为 PSD，
也不供应(132.11)。原含相位种子、实码的真零扩张、中心扇区、所有旁观与 return、
整个普通对偶和 proper 预算继续取原定义。
实际制备来源、记录与事件取得、完整控制仪器、原 Choi/CP 的全有限桥、
物理动力学、连续时间、物理钟、Hamiltonian、能量与 $\hbar$ 的实现和标定仍为原未决合同。

[T132VII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[T132VIII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md
[T132PinnedVIII]: https://github.com/the-omega-institute/trureturing/blob/76227a176b079ca94637adca93f6010bb0962a79/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md
[T132XI]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XI.md
[T132PTT]: https://arxiv.org/html/0904.3783v2
[T132Kye]: https://arxiv.org/html/2204.02516v2
[T132BK]: https://arxiv.org/html/1103.1884v1

## 追加锚（本行以下为增补区）

## 133. 三切口与正确块核条件不能把秩二联合切片提升为正性

**定义 133.1（抽象三切口与一个固定矩阵）。** 令
$H_0=H_1=H_2=\mathbb C^2$，均取固定计算基。
Hermitian 矩阵 $M$ 在第 $i$ 个单因子对其余因子的切口上块正，指

$$
(q\otimes w)^*M(q\otimes w)\ge0
\quad(q\in H_i,\ w\in\bigotimes_{j\ne i}H_j),
\tag{133.1}
$$

其中只按因子位置作酉置换，$w$ 不受可分性限制。在 $H_1\otimes H_2$ 上记

$$
\begin{aligned}
P&=|00\rangle\langle00|+|11\rangle\langle11|,&
Z&=|00\rangle\langle00|-|11\rangle\langle11|,\\
\eta&=|00\rangle+|11\rangle,&
A&=2P,\qquad B=2Z,\qquad C=I_4+2\eta\eta^*,\\
M_\star&=\begin{pmatrix}A&B\\B^*&C\end{pmatrix}
\quad\text{于 }H_0\otimes(H_1\otimes H_2).
\end{aligned}
\tag{133.2}
$$

这里 $M_\star$ 只是普通矩阵，不赋予它任何原 $E$ 或 $\mathcal K$ 成员资格。

**命题 133.2（最小局部维数的秩二相干障碍）。** 矩阵 $M_\star$ 满足全部三个
(133.1)，并有以下性质：

1. $q=|0\rangle$ 的条件**联合**矩阵
   $(q^*\otimes I_4)M_\star(q\otimes I_4)=A$ 为 PSD 且秩恰二。
2. 两个对角块均为 PSD，且同时满足正确取向的全局核与像条件

$$
\begin{gathered}
B^*\ker A=\{0\},\qquad B\ker C=\{0\},\\
\operatorname{ran}B\subseteq\operatorname{ran}A,\qquad
\operatorname{ran}B^*\subseteq\operatorname{ran}C.
\end{gathered}
\tag{133.3}
$$

3. 不同联合向量的相干不等式 VIII(128.28)仍严格失败，并存在
   $0\preceq F\preceq I_8$，使 $\operatorname{Tr}(F^TM_\star)=-1/2$。
   因此 $M_\star\not\succeq0$。

故“三个单因子切口块正、存在秩二条件联合切片、满足(133.3)”不能推出 PSD。
三因子各二维已足以反驳此蕴含；若任一因子一维，则不存在这样的反例。

证明。先固定任意复向量
$w=a|00\rangle+b|01\rangle+c|10\rangle+d|11\rangle$，令
$s=|a|^2+|d|^2$、$r=|b|^2+|c|^2$、$\delta=|a|^2-|d|^2$。
在 $H_1H_2$ 上用 $w$ 压缩后，留在 $H_0$ 上的矩阵为

$$
T_w=\begin{pmatrix}
2s&2\delta\\
2\delta&3s+r+4\operatorname{Re}(\overline a d)
\end{pmatrix}.
\tag{133.4}
$$

右下元至少为 $s+r\ge0$，因为
$2|a||d|\le s$。其行列式有精确复数证书

$$
\det T_w
=s^2+\bigl|s+4\overline a d\bigr|^2+2sr\ge0.
\tag{133.5}
$$

确实，展开行列式得
$2s^2+16|a|^2|d|^2+8s\operatorname{Re}(\overline a d)+2sr$，
正是右侧。两个主对角元非负及(133.5)给 $T_w\succeq0$，
故 $q^*T_wq\ge0$ 对所有复 $q\in H_0$ 成立，证明第一个切口。
此证书也包含 $s=0$、$w=0$，没有除以任何读数。

再固定任意复 $p=(p_0,p_1)^T\in H_1$，置
$x=|p_0|^2$、$y=|p_1|^2$、$D=\operatorname{diag}(1,-1)$。
在 $H_1$ 上压缩，按 $H_0\otimes H_2$ 排列所得矩阵为

$$
K_p=\begin{pmatrix}A_p&B_p\\B_p^*&C_p\end{pmatrix},\qquad
A_p=2\begin{pmatrix}x&0\\0&y\end{pmatrix},\quad
B_p=A_pD,\quad
C_p=\begin{pmatrix}
3x+y&2\overline p_0p_1\\
2\overline p_1p_0&x+3y
\end{pmatrix}.
\tag{133.6}
$$

它有不需要逆矩阵的 PSD 分解

$$
\begin{aligned}
K_p&=\begin{pmatrix}I_2\\D\end{pmatrix}A_p
       \begin{pmatrix}I_2&D\end{pmatrix}
       +\begin{pmatrix}0&0\\0&R_p\end{pmatrix},\\
R_p&=C_p-A_p
 =\begin{pmatrix}x+y&2\overline p_0p_1\\
                   2\overline p_1p_0&x+y\end{pmatrix}\\
 &=\begin{pmatrix}\overline p_0\\\overline p_1\end{pmatrix}
      \begin{pmatrix}p_0&p_1\end{pmatrix}
   +\begin{pmatrix}p_1\\p_0\end{pmatrix}
      \begin{pmatrix}\overline p_1&\overline p_0\end{pmatrix}\succeq0.
\end{aligned}
\tag{133.7}
$$

因此对每个复 $p$，$K_p\succeq0$，支付第二个切口的所有联合复向量。
$P,Z,\eta$ 均在交换 $H_1,H_2$ 下不变，故 $M_\star$ 也在该交换下不变；
将第二切口的同一分解运输到第三切口，证明全部(133.1)。
由有限谱分解及线性性，这还支付每个切口上的所有 PSD 产品效应及其正和，
而不只是三个因子全可分的效应。

第一条由 $A=2P$ 及 $P$ 的二维像立即得到。
为核对第二条，记 $S=\operatorname{span}\{|00\rangle,|11\rangle\}$。
有

$$
\ker A=\ker B=\ker B^*=S^\perp,\qquad
\operatorname{ran}A=\operatorname{ran}B=\operatorname{ran}B^*=S,
\qquad C\succeq I_4.
\tag{133.8}
$$

于是 $\ker C=\{0\}$、$\operatorname{ran}C=H_1\otimes H_2$，得到(133.3)。
这些取向来自块位置：对一般 PSD 块矩阵
$\left(\begin{smallmatrix}A&B\\B^*&C\end{smallmatrix}\right)$，
若 $u\in\ker A$，在 $(u,tv)$ 上对任意小复 $t$ 测试，线性项强制
$u^*Bv=0$ 对全部 $v$ 成立，即 $B^*u=0$；交换两块则给 $B\ker C=0$。
取正交补即为相应的像包含，而非把 $B$ 与 $B^*$ 的角色颠倒。

剩余失败是强度。令

$$
e_\pm=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
\quad
e_+^*Ae_+=2,\qquad e_-^*Ce_-=1,\qquad e_+^*Be_-=2.
\tag{133.9}
$$

所以 $|e_+^*Be_-|^2=4>2=(e_+^*Ae_+)(e_-^*Ce_-)$。
这两个不同的联合向量均可纠缠，不能由(133.4)中对同一个 $w$ 的测试替代。
用 Moore–Penrose 逆也可直接定位同一个缺口：$A^\dagger=P/2$，且

$$
B^*A^\dagger B=2P,\qquad
(C-B^*A^\dagger B)e_-=-e_-.
\tag{133.10}
$$

核条件已满足，却仍有负的 Schur 余项。这里仅使用成熟的块矩阵判据；
[Gallier，定理4.3][T133Gallier]给出实对称版本，其 Hermitian 版本的核方向如上，
余项恒等式则由在二次型中配方
$(u+A^\dagger Bv)^*A(u+A^\dagger Bv)+v^*(C-B^*A^\dagger B)v$
直接验证。

最后取单位实向量及其联合量子投影

$$
\begin{aligned}
h&=\frac{|0\rangle e_+-|1\rangle e_-}{\sqrt2}
  =\frac{|000\rangle+|011\rangle-|100\rangle+|111\rangle}{2},\\
F&=\overline h\,\overline h^*=hh^*,\qquad
0\preceq F\preceq I_8,\qquad
\operatorname{Tr}(F^TM_\star)=h^*M_\star h
 =\frac{2+1-4}{2}=-\frac12.
\end{aligned}
\tag{133.11}
$$

这遵守原全转置测试的取向，给出一个严格负的普通联合量子效应读数。
若三因子中任一维数为一，则在该因子对其余因子的切口上，
每个全空间向量都是产品向量，(133.1)本身就给 PSD。
因此二维、二维、二维是此反例的最小局部维数组合。证毕。

本命题的承重应用是排除 VIII(128.28)与132.4之间的一个秩二抽象推理路线，
归属为 repo-derived，不主张外部原创性。
对二可分混合态非负而对某联合态负的见证思想是成熟供应，参见
[Bourennane 等，式(1)—(2)及其前后的定义][T133Bourennane]；
标准 Schmidt 事实、块核条件及 Schur 判据不另列为新成果。
VIII128.2已供应原输出的三切口性质；132.4的秩至多一结论、
全部原复帽、整个原三输入锥与任意有限无界量子尺寸均保持原陈述。
(133.2)只证明这些抽象切口加秩二及正确核条件不足以自动支付相干强度。
没有从它取得原 $x,y,z\in E_3$、原 $X,Y,W\in\mathcal K$、
132.10的实际 $\Lambda$ 实现、源饱和或同源六份及 allN 补全；
132.7的整个原三角形、R3/R4、高中间次数、所有旁观、proper 预算与
全有限 min/max 产品律仍为原未决义务。

[T133Gallier]: https://www.cis.upenn.edu/~jean/schur-comp.pdf
[T133Bourennane]: https://arxiv.org/pdf/quant-ph/0309043v2

## 追加锚（本行以下为增补区）

## 134. 两条实际腿的普通 dyad 源桥与原输入秩一排除

### 134.A 固定源前件与普通 dyad 截面

**定义 134.1（同一个源上的两实际腿截面）。** 固定132.1及
[VIII123.1—123.2、125.1][T132VIII]的同一个
$\mathcal D,S,\mathcal K,E$，保留原实际标签、含相位计算基、
全部有限对象字和源箭头。取两条原实际 qutrit 腿 $A,B$；
它们的标签可以相同，但始终是两个位置。对每个正有限 $n$，记

$$
\begin{aligned}
\mathscr A_n&=A_{\mathcal D}(Q_nAB),&
\mathscr C_n&=E(Q_nAB),&
\mathscr B_n&=B_{\mathcal D}(Q_nAB),\\
\mathscr R_n&=\{\psi\psi^*:0\ne\psi\in
 \mathbb C^n\otimes\mathbb C^3\otimes\mathbb C^3\}.
\end{aligned}
\tag{134.1}
$$

$\mathscr R_n$ 只含普通正秩一矩阵。
$r_Q(\psi),r_A(\psi),r_B(\psi)$ 分别指对应单因子对其余因子的复 Schmidt 秩。
各层仍用 $b(H,L)=\operatorname{Tr}(H^TL)$、
$\mathscr B_n\subseteq\mathscr C_n\subseteq\mathscr A_n$；
不假定这些锥在全转置下不变。
本节只使用VIII123.2已付的源正性、低类型和双向角接口，
不取VIII124.1的 allN 产品律为前件。

**定理 134.2（两实际腿的普通 dyad 在源上下包络间无间隙）。**
在134.1的固定源前件下，对每个任意大的有限 $n$ 和每个非零 $\psi$，
有精确等价

$$
\boxed{
\begin{aligned}
\psi\psi^*\in\mathscr A_n
&\ \Longleftrightarrow\ \psi\psi^*\in\mathscr C_n
\ \Longleftrightarrow\ \psi\psi^*\in\mathscr B_n\\
&\ \Longleftrightarrow\
\bigl[r_Q(\psi)=1\ \text{或}\
 (r_A(\psi)\le2\ \text{且}\ r_B(\psi)\le2)\bigr].
\end{aligned}}
\tag{134.2}
$$

因此三个锥与 $\mathscr R_n$ 的交相等；零矩阵也属于三个锥。
右端是VIII124.4已有的分类形状，这里的结论是它在同一个
VIII123源的上下包络间成立，不需要该条目的完整 allN 前件。

证明。复用VIII125.1所列的精确低类型：纯量子字上的上下包络均为 PSD，
$Q_dA$ 上均为同一 $\mathcal K_{d,3}$，两实际腿上均为 $\mathrm{PSD}_9$。
源箭头分别保持 $A_{\mathcal D},E,B_{\mathcal D}$。
对上包络，这一点也可直接读成：若 $f:w\to v$、$e:v\to\mathbf1$
为源箭头，则 $ef$ 仍为源效应，故 $S(f)A_{\mathcal D}(w)\subseteq A_{\mathcal D}(v)$。
该推理对所有旁观字成立，只预合成效应，不张量两个任意上包络元素。

所需的单实际腿 dyad 排除准确复用VIII124.2的秩三压回论证，
其在这里的前件全由VIII123.2供给：
$\mathrm{SN}_2(d,3)\subseteq\mathcal K_{d,3}$、量子矩形合同正性，
以及 $\mathcal K_{3,3}$ 的整个迹一基之 $P$ 上界 $2/3$。
具体地，若 $\xi\xi^*\in\mathcal K_{d,3}$ 且 $r_A(\xi)=3$，
其 $d\times3$ 系数矩阵 $C$ 有复左逆 $L$；源量子合同
$\operatorname{Ad}_L$ 将此 dyad 送成 $\Omega_3$，
迫使 $P=\Omega_3/3\in\mathcal K_{3,3}$，与该上界矛盾。
这只是将既有单腿论证的每个前件对应到固定源，不调用 allN 的高阶角结论。

现设 $\psi\psi^*\in\mathscr A_n$ 且 $r_A(\psi)=3$。
对每个复两行矩阵 $L:B\to\mathbb C^2$，取二维等距嵌入
$J:\mathbb C^2\to B$，使 $\operatorname{ran}L^*\subseteq\operatorname{ran}J$，
则 $L=(LJ)J^*$。VIII123.2(v)分别支付 $\operatorname{Ad}_{J^*}:B\to Q_2$
和后接的量子合同 $\operatorname{Ad}_{LJ}$；连同旁观、重括号及置换，给源箭头

$$
Q_nAB\longrightarrow Q_nA Q_2\simeq Q_{2n}A,
\qquad
\psi\psi^*\longmapsto\psi_L\psi_L^*,
\quad \psi_L=(I_Q\otimes I_A\otimes L)\psi,
\tag{134.3}
$$

其中向量的最后识别只作规范置换。
输出在 $A_{\mathcal D}(Q_{2n}A)=\mathcal K_{2n,3}$，
故由单腿排除，其 $A\mid Q_nQ_2$ 秩至多二，包括零输出。
直接应用VIII124.3的两行刚性引理，参数取该处 $Q=\mathbb C^n$，
得到 $\psi=q_Q\otimes\chi_{AB}$，其中 $\chi$ 的 Schmidt 秩为三，
从而 $r_Q(\psi)=1$。
若先有 $r_B(\psi)=3$，用原位置置换交换 $A,B$ 后应用同一引理。
若两者都不是三，二者均至多二。由此得到(134.2)最左端蕴含最右端。

反向须取得源成员，而不只取得 $E$ 成员。
若 $r_A,r_B\le2$，分别取支撑的复等距嵌入
$J_A:\mathbb C^{d_A}\to\mathbb C^3$、
$J_B:\mathbb C^{d_B}\to\mathbb C^3$，其中 $1\le d_A,d_B\le2$。
存在纯量子向量 $\widetilde\psi\in\mathbb C^n\otimes\mathbb C^{d_A}
\otimes\mathbb C^{d_B}$，使
$\psi=(I_Q\otimes J_A\otimes J_B)\widetilde\psi$。
先用量子源态 $\widetilde\psi\widetilde\psi^*$，再分别使用VIII123.2(v)
的源嵌入 $\operatorname{Ad}_{J_A},\operatorname{Ad}_{J_B}$，即得源态
$\psi\psi^*$。这两个嵌入各自作用于一条实际输出，不是集体实际 CP。

若 $r_Q=1$，写 $\psi=q\otimes\chi$。
VIII123.2(iv)已给每个 $\chi\chi^*$ 的实际两腿源态构造：
一个原实际杯后接一体复矩形合同，并按需要运输实际标签。
$qq^*$ 也是量子源态；这两个源态箭头的张量积是源态箭头，
恰给 $\psi\psi^*$。
两种情况下均已属于 $\mathscr B_n$，不需要任意两个 $E$ 输入的最小锥界。
最后用 $\mathscr B_n\subseteq\mathscr C_n\subseteq\mathscr A_n$
闭合所有等价。

为保持原 proper 预算，取 $c_L=\max(1,\|L\|_{\rm op})$，
用 $L/c_L$ 实现；归一 dyad 的实际输出质量为
$\|\psi_L\|^2/(c_L^2\|\psi\|^2)\in[0,1]$。
上述左逆合同也作同样正缩放，矛盾仍由非零 $\Omega_3$ 射线得到。
支撑嵌入保迹，所有压缩的迹亏损与 proper 效应延拓连同旁观者
均沿VIII123.2(v)、式(123.14)使用。
未缩放 dyad 的恢复只是正锥数乘，不声称成功分支质量为一或新增物理制备。证毕。

### 134.B 原规范三角形的输入秩一消费者

**推论 134.3（原压缩输入秩至多一时无规范负三角形）。**
取132.1的任意合法 $x,y,z,Y,W$，以132.3的原压缩 $q$ 令
$H=qx\in\mathscr C_2=E(Q_2A_1A_2)$。
若普通环境矩阵秩 $\operatorname{rank}H\le1$，则

$$
M^0_{Y,W}(x,y,z)
 =(\mathrm{id}_2\otimes\Lambda)(H)\succeq0,
\qquad
\operatorname{Tr}\bigl(F^TM^0_{Y,W}(x,y,z)\bigr)\ge0
\quad(F\succeq0).
\tag{134.4}
$$

量词保留任意有限无界 $\ell,m$ 和其余数据的整个原输入锥；
不要求 $y,z$ 为 PSD，也不要求 $Y,W$ 为 $\mathrm{SN}_2$。
此处是输入 $qx$ 的秩，与132.4中一个条件联合输出的秩不同。

证明。若 $H=0$，结论由线性得到。
否则 $H$ Hermitian、秩一，且VIII123.2的严格正迹给 $\operatorname{Tr}H>0$。
因此 $H=\psi\psi^*$ 对某非零复向量 $\psi$ 成立，
不是负的秩一矩阵。由134.2，$H\in\mathscr B_2$。
对每个固定的合法 $y,z,Y,W$，直接应用132.3第1项的源完全正性，
再用(132.13)的精确恒等式即得 PSD。
全转置将 PSD 效应 $F$ 送到 PSD 矩阵 $F^T$，故最后读数非负。
只在效应上使用这个普通矩阵事实，不给 $E$ 添加转置正性或普通 CP 层。
全部源旁观和高中间次数由132.3第1项的原量词保留；
proper 帽与输出质量仍取132.5的原归一，未对零质量作条件化。证毕。

### 134.C 数学归属与适用边界

**约定 134.4（源前件桥的归属与未决域）。** 134.2—134.3是固定源下的
仓内综合推导（repo-derived）；新增承重内容是只用已付源箭头，
从上包络中的两实际腿 dyad 得到下包络成员，再直接消费132.3第1项。
VIII124.4的分类形状、VIII124.3的两行线性刚性、VIII123.2的低类型与
双向源角、VIII126的原端口标准形和132.3的源完全正性均是已有供应。
不另计 Schmidt 分解、线性支撑、矩形左逆或源效应预合成为新数学内容。

De les Coves—van der Eyden—Netzer，
[*Beyond Operator Systems*, arXiv:2312.13983v1][T134Beyond]，
定义3.1—3.2及引理3.5(i)—(iii)给出 stem、源上下包络的对偶及源箭头正性；
本节以VIII123的固定 $\mathcal D,S$ 实例化这些概念，
不由一般锥系统结论推断任意上包络元素的张量闭包。
Terhal—Horodecki，
[*A Schmidt number for density matrices*, quant-ph/9911117v4][T134Schmidt]，
定义1给出 Schmidt 数的 dyad 分解约定，纯态时即 Schmidt 秩。
该文处理普通量子密度矩阵，不供应本源的混合矩阵锥相等；
两行刚性的准确供应仍是VIII124.3。
上述来源不被归为本源桥的既有完整证明，也不据此主张外部优先权。

(134.2)只比较普通正 dyad 截面，既不推出
$\mathscr A_n=\mathscr C_n=\mathscr B_n$，也不分类任一锥的全部极端射线。
普通 PSD 混合矩阵的谱分量不自动属于这些锥，不能逐谱分量推广本定理。
134.3只支付指定压缩输入秩至多一的规范族；
全部复帽与其它 $\mathrm{SN}_2$ 门户的传递仍准确取132.2，
输入秩条件须施于其中实际产生的压缩输入，不能从未变换的 $qx$ 自动传递。
本节没有构造新的未知锥族，也没有取得同源负三角形。

对整个 $\mathscr C_2$ 的(132.11)、VIII(128.28)的全相干强度、
其余原三角形、完整 R3/R4、同源六份及全部有限原产品律仍未解决。
原种子相位、真零扩张、整个普通对偶与 proper 预算均保持原条件。
XI148的忠实 PSD 截面及其各项 EB3、$\mathsf{Conn}$、ZC 前件
不由本节取得，也不被用来断言这些混合锥为 PSD。
实际来源、事件与仪器取得、物理动力学、连续时间、物理钟、
Hamiltonian、能量与 $\hbar$ 的实现及标定仍取132.7的未决合同。

[T134Beyond]: https://arxiv.org/html/2312.13983v1
[T134Schmidt]: https://arxiv.org/html/quant-ph/9911117v4

## 追加锚（本行以下为增补区）

## 135. 同一共同源的算子系统端点与原两实际腿锚的严格分离

**定义 135.1（固定源、复矩阵序与两个端点配方）。** 固定
[VIII123.1—123.2][T132VIII]的任一个共同族 $\mathcal K$，以及由它生成的
同一个 $\mathcal D,S$；原标签、含相位计算基和所有源箭头不变。
取其中一个实际 qutrit 扇区 $A_s$，$n_s=3$。在复向量空间
$\mathcal O=M_3(\mathbb C)$ 上用通常的伴随，并指定

$$
C_k=M_k(\mathcal O)^+=\mathcal K_{k,3},\qquad e=I_3,
\qquad \delta=\operatorname{Tr}/3,\qquad k\ge1.
\tag{135.1}
$$

这里 $e$ 是辅助算子系统的矩阵序单位；原物理归一单位始终是泛函
$u_s=\operatorname{Tr}$。复对偶记为 $\mathcal O^d$，其矩阵序定义为
$[f_{ij}]\ge0$ 当且仅当 $L\mapsto[f_{ij}(L)]$ 完全正，
选定的对偶算子系统单位为 $\delta$。这些单位不相互替换。

以下 $\min_{\mathrm{OS}},\max_{\mathrm{OS}}$ 专指通常的复算子系统张量积，
与VII102中仅用标量锥定义的 $\min,\max$ 产品不同。
核性指对每个复算子系统 $\mathcal R$，恒等识别下的
$\mathcal R\otimes_{\min_{\rm OS}}\mathcal O$ 与
$\mathcal R\otimes_{\max_{\rm OS}}\mathcal O$ 在所有有限矩阵层具有相同正锥。
为固定其含义，最小张量积在第 $r$ 层的正元由所有有限矩阵值 UCP 映射
$\phi,\psi$ 的测试 $(\phi\otimes\psi)^{(r)}(Z)\succeq0$ 定义；
最大张量积的第 $r$ 层是下列锥的 Archimedean 化：

$$
\begin{aligned}
\mathscr P_r
 &=\{\alpha(X\otimes Y)\alpha^*:
 X\in C_p,\ Y\in C_q,\ \alpha\in M_{r,pq}(\mathbb C),\ p,q\ge1\},\\
D_{\max,r}
 &=\{Z=Z^*:Z+\varepsilon I_r\otimes e\otimes e\in\mathscr P_r
                   \text{ 对每个 }\varepsilon>0\},\\
D_{\tau,r}
 &=M_r(\mathcal O\otimes_\tau\mathcal O)^+,
\qquad D_\tau=D_{\tau,1}.
\end{aligned}
\tag{135.2}
$$

此处 $X\otimes Y$ 的矩阵指标按通常次序分组。
$D_\tau$ 的载体始终是原 $A_sA_s$ 的
$\operatorname{Herm}_3\otimes_{\mathbb R}\operatorname{Herm}_3
\simeq\operatorname{Herm}_9$，不把实际对象改型。
在这个载体上，$T_{AA}$ 是原计算基全转置，
$K^*$ 是整个普通迹对偶，$K^\vee=T_{AA}K^*$。
取原杯帽

$$
\eta=\sum_{i=0}^2|ii\rangle,\qquad
\Omega=\eta\eta^*=\sum_{i,j=0}^2E_{ij}\otimes E_{ij},
\qquad \beta(Z)=\operatorname{Tr}(\Omega Z).
\tag{135.3}
$$

**定理 135.2（原共同族的严格 OS 端点排除）。** 对定义135.1的每一个固定源，
(135.1)在所有有限复矩阵层构成一个 Archimedean 算子系统。
复线性映射

$$
J:\mathcal O\longrightarrow\mathcal O^d,
\qquad J(H)(L)=\operatorname{Tr}(H^T L)
\tag{135.4}
$$

是完全序同构，$J(e)=\operatorname{Tr}=3\delta$，
故 $J/3$ 是所选单位下的幺完全序同构。这个算子系统不是
$(\min_{\mathrm{OS}},\max_{\mathrm{OS}})$-核的。在原 $A_sA_s$ 坐标中有

$$
\begin{gathered}
D_{\max}\subsetneq\mathrm{PSD}_9\subsetneq D_{\min},\\
D_{\min}^{\vee}=D_{\max},\qquad D_{\max}^{\vee}=D_{\min},\\
D_{\min}^{*}=T_{AA}D_{\max},\qquad
D_{\max}^{*}=T_{AA}D_{\min},\\
\Omega/3\notin D_{\max},\qquad
\exists z\in D_{\min}:\quad
\operatorname{Tr}z=1,\quad (\beta/3)(z)<0.
\end{gathered}
\tag{135.5}
$$

完全 min/max 对偶性在每个有限参考层成立；(135.5)中与普通 PSD 的严格夹逼
只断言标量参考层 $r=1$。不要求任何源锥在全转置或部分转置下不变。

分别固定 $\tau=\min_{\mathrm{OS}}$ 或 $\tau=\max_{\mathrm{OS}}$，令

$$
H^\tau_{a;r}=M_r(\mathcal O^{\otimes_\tau a})^+,
\qquad \mathcal O^{\otimes_\tau0}=\mathbb C.
\tag{135.6}
$$

这两个各自固定的张量幂配方对称、结合，且在所有有限 $r$ 保留
$H^\tau_{0;r}=\mathrm{PSD}_r$、$H^\tau_{1;r}=\mathcal K_{r,3}$。
两者都不满足原来必需的 $H_{2;1}=\mathrm{PSD}_9$：最大配方失去原归一杯，
最小配方使同一个原 proper 帽 $\beta/3$ 失去正性。
这个帽在必需的 PSD 锚上的整个互补效应预算为

$$
\beta/3\ \longleftrightarrow\ \Omega/3,\qquad
u_{ss}-\beta/3\ \longleftrightarrow\ I_9-\Omega/3\succeq0,
\qquad u_{ss}=\operatorname{Tr}.
\tag{135.7}
$$

因此排除的量词只遍历这些共同族及其两个固定 OS 端点配方。
$z$ 属于被排除的最小配方，不是合法原三角形的负概率见证；
结论不排除中间张量积、同一源的其它补全或其它 $t<1$ 的源。

**证明。** 所有用到的源性质均取VIII123.2：
$\mathrm{SN}_2(k,3)\subseteq C_k\subseteq\mathrm{BP}_2(k,3)$、
$C_k^\vee=C_k$、两个因子上独立复矩形合同及 CP 正性，
以及 $B_-=(2I_9-\Omega)/5\in C_3$。
特别地 $C_1=\mathrm{PSD}_3$、$C_2=\mathrm{PSD}_6$。
本证明不重新选取 $\mathcal K$，也不改变其固定源的高阶部分。

先验证复算子系统的前提。每个 $C_k$ 是通常伴随下自伴部分的闭尖锥。
矩形标量矩阵压缩就是第一因子上的源合同，故
$A^*C_kA\subseteq C_\ell$，$A\in M_{k,\ell}(\mathbb C)$。
两个直和嵌入及加法给 $C_k\oplus C_\ell\subseteq C_{k+\ell}$，
反向坐标压缩给直和正性所需的反向条件。

每个 $I_k\otimes I_3$ 都在可分锥的内部，因而在 $C_k$ 的内部。
这里可以直接选取有限个局部秩一投影：计算基投影，以及对每对不同基向量
由 $|a\rangle\pm|b\rangle$、$|a\rangle\pm i|b\rangle$ 归一化所得的投影。
它们张成整个局部 Hermitian 实空间，其和是恒等矩阵的正倍数。
两边取乘积后仍张成整个张量空间，且恒等矩阵是这些生成元的严格正系数组合，
所以是它们所生有限锥的内点。这同时给任意自伴 $Z$ 的
$tI_k\otimes e\pm Z\in C_k$，只需 $t$ 足够大。
闭性又给出 Archimedean 条件：若 $Z+\varepsilon I_k\otimes e\in C_k$
对每个 $\varepsilon>0$ 成立，则 $Z\in C_k$。
因此(135.1)确实满足所有有限复层的矩阵序与单位公理。

再验证(135.4)，不能只用标量自对偶。通常伴随与复线性显然相容。
对 $H=[H_{ij}]\in M_k(\mathcal O)_{\rm sa}$、
$L=[L_{ab}]\in C_\ell$，其矩阵测试是

$$
Z_{ia,jb}=J(H_{ij})(L_{ab})
        =\sum_{c,d=0}^2 H_{ic,jd}L_{ac,bd}.
\tag{135.8}
$$

若 $H\in C_k$，这正是VIII(123.8)—(123.9)的共同族 Bell 收缩，
所以 $Z\succeq0$；其中任意复测试矩阵、矩形合同及 $C_k^\vee=C_k$
都已包含在该源恒等式中。于是 $J^{(k)}(H)$ 正。
反之，若 $L\mapsto[J(H_{ij})(L)]$ 完全正，令 $\ell=k$，
对(135.8)使用向量 $\sum_i|ii\rangle$，得到

$$
\sum_{i,j}J(H_{ij})(L_{ij})
       =\operatorname{Tr}(H^T L)\ge0\qquad(L\in C_k).
\tag{135.9}
$$

故 $H\in C_k^\vee=C_k$。非退化迹配对给复线性双射，
从而 $J$ 及其逆在所有有限层完全正。
由于 $\delta(e)=1$ 且 $C_1=\mathrm{PSD}_3$，$\delta$ 是忠实态。
Kavruk，[*Nuclearity Related Properties in Operator Systems*,
arXiv:1107.2133v4][T135Kavruk] §1.2、定理1.3的有限维忠实态单位定理
适用于此九维复空间；所选对偶单位确为 $\delta$。
$J(e)=3\delta$ 给所声称的全部单位常数，原物理单位仍为 $3\delta$。

这个具体 $\mathcal O$ 的非核性由低层和固定 $B_-$ 一起强制。
若它是核的，Han—Paulsen，[*An Approximation Theorem for Nuclear Operator Systems*,
arXiv:1009.2541v4][T135HP]推论3.7给一个有限维 C* 代数 $\mathcal B$
及幺完全序同构 $\theta:\mathcal O\to\mathcal B$。
因为前两层就是普通 $M_3$ 的前两层，将 $\theta$ 及其逆看作
普通 C* 代数间的映射时，二者均为幺二正映射。
对普通 $a\in M_3$ 的正块矩阵
$\left(\begin{smallmatrix}a^*a&a^*\\a&I_3\end{smallmatrix}\right)$
应用二正性，Schur 补给

$$
\theta(a^*a)\succeq\theta(a)^*\theta(a),\qquad
\theta^{-1}(\theta(a)^*\theta(a))\succeq a^*a.
\tag{135.10}
$$

第一式再应用正映射 $\theta^{-1}$，迫使两式均取等。
极化得 $\theta(a^*b)=\theta(a)^*\theta(b)$，故 $\theta$ 实为
普通 $M_3$ 到 $\mathcal B$ 的幺 * 同构。
因此其在每一矩阵层运输的正锥只能是普通 PSD。
可是 $B_-\in M_3(\mathcal O)^+$，而
$B_-\eta=-\eta/5$。这与完全序同构矛盾。
这里没有由标量锥单独推断高层，也未假定源的转置不变性。

接下来在标量参考层定位原锚。
对(135.2)中 $r=1$ 的生成元，写 $X=[X_{ij}]\in C_p$、
$Y=[Y_{ab}]\in C_q$。它在原 $A_sA_s$ 上的矩阵是

$$
W=\sum_{i,j,a,b}\alpha_{ia}\overline{\alpha_{jb}}
                              X_{ij}\otimes Y_{ab}.
\tag{135.11}
$$

$X,Y$ 各自是既定源的形式态生成元，故二者的张量积是源态；
源置换将两个量子端口并置，再用量子 CP 效应
$R\mapsto\alpha R\alpha^*$，恰得到(135.11)。
这一步使用的是两个源生成元的张量，而非任意 $E$ 元素的制备或张量闭包。
VIII123.2(iv)已给
$B_{\mathcal D}(A_sA_s)=\mathrm{PSD}_9$，所以 $W\succeq0$。
对 $Z\in D_{\max}$，每个 $Z+\varepsilon I_9$ 都在上述原始锥中，
令 $\varepsilon\downarrow0$，由 PSD 的闭性得到

$$
D_{\max}\subseteq\mathrm{PSD}_9.
\tag{135.12}
$$

这里 $\alpha$ 只有一个输出行；若留下 $r$ 维量子输出，
同一源论证只落入 $B_{\mathcal D}(Q_rA_sA_s)$，并不落入
普通 $\mathrm{PSD}_{9r}$。这准确保留VIII128.4的混合锚边界。

为取完整对偶，使用[T135Kavruk]定理6.3的有限维 min/max 完全对偶性。
它在此处给出幺完全序同构

$$
\begin{aligned}
(\mathcal O\otimes_{\max_{\rm OS}}\mathcal O)^d
   &\simeq\mathcal O^d\otimes_{\min_{\rm OS}}\mathcal O^d,\\
(\mathcal O\otimes_{\min_{\rm OS}}\mathcal O)^d
   &\simeq\mathcal O^d\otimes_{\max_{\rm OS}}\mathcal O^d.
\end{aligned}
\tag{135.13}
$$

因子对偶单位取 $\delta$，张量对偶单位取忠实态
$\delta\otimes\delta=\operatorname{Tr}/9$。
用 $J/3$ 运输两个因子时，得到的泛函是原双线性配对的 $1/9$ 倍：

$$
((J/3)\otimes(J/3))(H)(L)
       =\tfrac19\operatorname{Tr}(H^T L).
\tag{135.14}
$$

所以正标量不改变锥，标量层恰给
$D_{\min}^\vee=D_{\max}$、$D_{\max}^\vee=D_{\min}$。
(135.13)是所有有限层的完全序结论，不附带任何高参考层 PSD 等式。
由 $K^\vee=T_{AA}K^*$ 及 $T_{AA}^2=1$，立即得到(135.5)中的两个
整个普通迹对偶等式。对(135.12)取 $\vee$，用
$\mathrm{PSD}_9^\vee=\mathrm{PSD}_9$，亦得
$\mathrm{PSD}_9\subseteq D_{\min}$。

还须把严格性精确放在原杯上，不能只说非核系统的某些乘积不同。
令

$$
\mathfrak c=(J\otimes\mathrm{id})(\Omega)
        =\sum_{i,j}J(E_{ij})\otimes E_{ij}
        \in\mathcal O^d\otimes\mathcal O.
\tag{135.15}
$$

由于 $J(E_{ij})(L)=L_{ij}$，这个张量所对应的映射
$\mathcal O\to\mathcal O$ 正是恒等映射。
[T135Kavruk]命题6.1的最小张量正元—完全正映射对应适用于有限维
$\mathcal O^d$，并以规范双对偶识别 $\mathcal O^{dd}=\mathcal O$；
因而 $\mathfrak c$ 是最小张量正元。

若原杯 $\Omega$ 在 $D_{\max}$ 中，
$(J/3)\otimes\mathrm{id}$ 的幺完全序同构性给
$\mathfrak c/3$、因而 $\mathfrak c$ 在
$(\mathcal O^d\otimes_{\max_{\rm OS}}\mathcal O)^+$ 中。
现将[T135HP]定理3.1证明中的规范张量分解及支撑正规化用于这个具体张量。
该定理的陈述以幺 CP 映射和任意有限维测试系统为条件；
这里并不把单个张量的正性冒充全部测试条件，而是直接给出其所需的逼近：
由最大锥的定义，对每个 $\varepsilon>0$ 可写

$$
\mathfrak c+\varepsilon\delta\otimes e
   =\alpha(P\otimes Q)\alpha^*,\qquad
P\in M_n(\mathcal O^d)^+,\quad Q\in M_m(\mathcal O)^+.
\tag{135.16}
$$

写 $P=[f_{ij}]$。映射 $f:x\mapsto[f_{ij}(x)]$ 完全正，
$g:M_n\to\mathcal O$、$g(A)=\alpha(A\otimes Q)\alpha^*$ 也完全正，
后者的各层正性直接由矩阵序压缩得到。逐项求值(135.16)给

$$
gf(x)=x+\varepsilon\delta(x)e.
\tag{135.17}
$$

令 $a=f(e)\succeq0$、$p=\operatorname{supp}a$。
由 $-te\le x\le te$ 对每个自伴 $x$ 可取 $t$，得
$-ta\le f(x)\le ta$，故 $f(x)=pf(x)p$；复线性给全部 $x$。
$a$ 在 $pM_np$ 中可逆，且 $p\ne0$，因为 $gf(e)=(1+\varepsilon)e$。
只在这个有限支撑角内取逆，定义

$$
\varphi_\varepsilon(x)=a^{-1/2}f(x)a^{-1/2},\qquad
\psi_\varepsilon(A)=\frac{g(a^{1/2}Aa^{1/2})}{1+\varepsilon}.
\tag{135.18}
$$

将 $pM_np$ 幺识别为 $M_{\operatorname{rank}p}$，两映射均为 UCP，且

$$
\psi_\varepsilon\varphi_\varepsilon(x)
       =\frac{x+\varepsilon\delta(x)e}{1+\varepsilon}
       \longrightarrow x.
\tag{135.19}
$$

这正满足[T135HP]推论3.2的点范数 UCP 矩阵分解条件，故迫使 $\mathcal O$ 核。
支撑压缩没有假定 $a$ 在整个 $M_n$ 可逆；因定义域已是整个有限维
$\mathcal O$，也不需要额外的扩张映射或物理制备。
这与已经证明的源特定非核性矛盾，故 $\Omega\notin D_{\max}$。
锥的齐次性给 $\Omega/3\notin D_{\max}$，而它是普通 PSD 的迹一元素，
证明(135.12)严格。

由 $D_{\min}^\vee=D_{\max}$ 及 $\Omega\notin D_{\max}$，
存在 $z_0\in D_{\min}$ 满足
$b(z_0,\Omega)<0$。由于 $\Omega^T=\Omega$，此值就是
$\operatorname{Tr}(\Omega z_0)$。
所有普通局部向量态在 $C_1=\mathrm{PSD}_3$ 上正，因而是标量值 CP 映射；
用最小张量积的乘积态测试可知 $D_{\min}\subseteq\mathrm{BP}_1(3,3)$。
因 $I_9$ 可分，$\operatorname{Tr}z_0\ge0$。又 $z_0\ne0$；
若 $\operatorname{Tr}z_0=0$，则这个非零块正泛函在可分锥的内点 $I_9$ 上为零，
正负小扰动将迫使它在整个空间为零，矛盾。因此 $\operatorname{Tr}z_0>0$。
故 $z=z_0/\operatorname{Tr}z_0$ 给(135.5)的归一负帽读数。
普通 PSD 上 $\operatorname{Tr}(\Omega z)\ge0$，所以这个 $z$ 不在 PSD 锚中，
第二个包含也严格。正标量归一保持最小锥成员与负帽符号。

最后，$\Omega$ 的本征值为三及零，故(135.7)的两个效应矩阵都 PSD，
且和恰为 $I_9$。这是整个普通对偶区间 $[0,u_{ss}]$ 中的互补效应对。
VIII123.2(v)的全原帽在每个对角中心扇区取 $\Omega_i/3$，
在非对角扇区取零；因 $n_i\le3$，其互补块分别为
$I_{n_i^2}-\Omega_i/3\succeq0$ 及相应恒等矩阵。
故整个原直和的 proper 预算仍完整支付，且在 $A_sA_s$ 上的限制恰为此处的 $\beta/3$。
原杯 $\Omega/3$ 的迹为一，而同一原帽作用于最小配方的 $z$ 得到负值；
这只说明该配方不容许保留原帽，不产生原模型内的负事件。

Kavruk—Paulsen—Todorov—Tomforde，[*Tensor Products of Operator Systems*,
arXiv:0910.2210v3][T135KPTT]定理4.6、5.5分别给两个张量积的
对称性、结合性及函子性，故每个单独固定的配方(135.6)具有这些性质。
矩阵代数因子的 min/max 一致与通常矩阵放大识别，亦见
[T135HP]定理3.1证明，给所有有限参考层的一实际腿锥恰为 $C_r$。
这些结论不把两实际腿变成矩阵代数对象。
[T135KPTT]定理5.8的联合完全正泛性质也不供应
$D_{\max,r}\subseteq\mathrm{PSD}_{9r}$；此处没有假定未知的集体实际 CP。
原两实际腿锚已在 $r=1$ 失败，所以对称结合的端点幂并非所求的原全有限补全。

承重结论是VIII123的同一源、原杯帽和两个 OS 端点间的上述对应与严格排除，
为仓内综合推导（repo-derived）；所用一般 OS 对偶、逼近与张量性质
仅作为各相应步骤的文献工具（literature-attested），不据此主张外部新颖性或优先权。
这不是VIII124.6—124.10的匹配锥端点，也不把VIII129.2的另一源通用障碍
移用于当前源；VII105.7的张量稳定映射捷径与IX132—134的实际 return／dyad 桥
均未补入任何混合锥等式。
同源六份、R3/R4、所有旁观字、任意高有限中间源次数、原扇区／相位／码、
真零扩张、整个普通对偶及全部产品与预算条件仍须在同一个原全有限模型中满足。
本定理既不取得源饱和、$S_3$、任意 $E$ 准备或物理供应，
也不推出 Fusion3、$t=1$、其它统一 $t_0<1$ 的存在或不可能性，
更不提供物理时间、钟或 $\hbar$。证毕。

[T135HP]: https://arxiv.org/html/1009.2541v4
[T135Kavruk]: https://arxiv.org/html/1107.2133v4
[T135KPTT]: https://arxiv.org/html/0910.2210v3

## 追加锚（本行以下为增补区）

## 136. 原混合输入的收缩秩二源证书与 IX132 负见证约束

### 136.A 固定原源、收缩秩与可用的产品测试

**定义 136.1（两实际腿的原混合收缩）。** 固定 VIII123.1—123.2、125.1
及本卷132.1的同一个 $\mathcal D,S,\mathcal K,E$、同一实际标签和同一计算基。
取其中的实际 qutrit 扇区 $A_s$，并对每个有限正整数 $n$ 写

$$
 B_n=B_{\mathcal D}(Q_nA_sA_s),\qquad
 C_n=E(Q_nA_sA_s),\qquad
 A_n=A_{\mathcal D}(Q_nA_sA_s).
\tag{136.1}
$$

对 $H\in\operatorname{Herm}_n\otimes_{\mathbb R}\operatorname{Herm}_9$ 定义实线性
收缩映射 $R_H:\operatorname{Herm}_n\to\operatorname{Herm}_9$ 为

$$
 \operatorname{Tr}(G R_H(F))=\operatorname{Tr}((F\otimes G)H)
 \qquad(F\in\operatorname{Herm}_n,\ G\in\operatorname{Herm}_9),
\tag{136.2}
$$

并令 $r(H)=\dim_{\mathbb R}\operatorname{im}R_H$。这个秩是量子参考腿与
两个实际腿的 Hermitian 张量收缩秩；它不是普通矩阵秩，也不是向量的 Schmidt 秩。

VIII123.2 的源态条款逐个给出每个 $F\in\operatorname{PSD}_n$ 的量子源态，
以及每个 $G\in\operatorname{PSD}_9$ 的原实际两腿源态。将这两个从单位出发的
源箭头作原有的张量、规范重括号和位置线，得到同一原源上的箭头，因此

$$
 \operatorname{PSD}_n\otimes\operatorname{PSD}_9\subseteq B_n.
\tag{136.3}
$$

这里分别使用两条已支付的一体源箭头；(136.3) 不把两个任意 $E$ 元素相乘，
也不加入两实际腿的集体 CP 映射。特别地，实际因子是原来的两个位置，
而不是把 $A_sA_s$ 改名为一个免费实际对象。

### 136.B 秩至多二的完整源分解

**定理 136.2（原上包络中的收缩秩二证书）。** 对每个有限正整数 $n$ 和每个
$H\in A_n$，若 $r(H)\le2$，则存在 $0\le r(H)$ 个（零项时为空和）矩阵

$$
 U_j\in\operatorname{PSD}_n,\qquad V_j\in\operatorname{PSD}_9,\qquad
 H=\sum_{j=1}^{r(H)}U_j\otimes V_j .
\tag{136.4}
$$

因而 $H\in B_n$。这条结论在 $H$ 进入时不假定普通 PSD。

**证明。** 先把原配对的转置方向写清。任取
$F\in\operatorname{PSD}_n$、$G\in\operatorname{PSD}_9$，则
$F^{T}\otimes G^{T}\in B_n$，由(136.3)和 $H\in A_n$ 得

$$
 0\le b(H,F^T\otimes G^T)
   =\operatorname{Tr}\!\left(H^T(F^T\otimes G^T)\right)
   =\operatorname{Tr}\!\left((F\otimes G)H\right).
\tag{136.5}
$$

于是对每个 $F\ge0$ 和全部 $G\ge0$，(136.2)给出
$\operatorname{Tr}(G R_H(F))\ge0$。普通 PSD 锥在 Hermitian 实空间中的迹对偶
仍是自身，所以

$$
 R_H(\operatorname{PSD}_n)\subseteq\operatorname{PSD}_9.
\tag{136.6}
$$

这一步才从原全转置极性取得普通正性；没有把 $H$ 预先当作普通 PSD。

置 $V=\operatorname{im}R_H$、$C=R_H(\operatorname{PSD}_n)$。谱分解说明
$\operatorname{PSD}_n$ 在 $\operatorname{Herm}_n$ 中实张成整个空间，故
$\operatorname{span}_{\mathbb R}C=V$ 且 $\dim V=r(H)$。

若 $r(H)=0$，则 $R_H=0$。由(136.2)的非退化性，$H=0$，得到空和。
若 $r(H)=1$，取 $0\ne V_1\in C$；(136.6)给 $V_1\ge0$，并写
$R_H(F)=f_1(F)V_1$。系数泛函 $f_1$ 在 $\operatorname{PSD}_n$ 上非负，
故 PSD 锥的自对偶性给唯一 $U_1\ge0$ 使
$f_1(F)=\operatorname{Tr}(U_1F)$。

设 $r(H)=2$。闭包 $\overline C$ 是二维 $V$ 中的闭、凸、尖锥；它仍包含于
$\operatorname{PSD}_9$，且张成 $V$。二维尖锥的两个边界射线可取非零生成元
$V_1,V_2\in\operatorname{PSD}_9$。因此每个 $c\in C$ 唯一写成
$c=\alpha_1V_1+\alpha_2V_2$，其中 $\alpha_1,\alpha_2\ge0$。
令 $f_j$ 为这两个坐标泛函与 $R_H$ 的复合。它们是实线性泛函且在
$\operatorname{PSD}_n$ 上非负，故存在 $U_j\in\operatorname{PSD}_n$ 使

$$
 R_H(F)=\operatorname{Tr}(U_1F)V_1+\operatorname{Tr}(U_2F)V_2
 \qquad(F\in\operatorname{Herm}_n).
\tag{136.7}
$$

由(136.2)、(136.7)及简单张量的实张成性，迹配对的非退化性给出

$$
 H=U_1\otimes V_1+U_2\otimes V_2.
\tag{136.8}
$$

这同时证明了 $r=1$ 的式(136.4)，并说明 $r\le2$ 时 $H$ 实际是普通 PSD。
式(136.3)逐项把(136.4)的每个乘积送入 $B_n$，再用其凸锥闭合，得到
$H\in B_n$。∎

若 $H\ne0$，还可在原 proper 预算内归一化。乘积 PSD 锥含有
$I_n\otimes I_9$ 的内点，故非零 $H\in A_n$ 满足
$\operatorname{Tr}H=b(H,I_n\otimes I_9)>0$。删去(136.4)中的零项，置

$$
 \widehat U_j=\frac{U_j}{\operatorname{Tr}U_j},\qquad
 \widehat V_j=\frac{V_j}{\operatorname{Tr}V_j},\qquad
 \lambda_j=\frac{\operatorname{Tr}U_j\,\operatorname{Tr}V_j}{\operatorname{Tr}H}.
\tag{136.9}
$$

则 $\lambda_j\ge0$、$\sum_j\lambda_j=1$，且
$H/\operatorname{Tr}H=\sum_j\lambda_j\widehat U_j\otimes\widehat V_j$。
这只是原源锥中的有限凸组合：每个有非零迹的因子按原迹一 proper 约定归一，
零矩阵不作条件化，也不由此声称一个确定性物理制备或成功率为一。
当 $n=1$ 时 $\dim_{\mathbb R}\operatorname{Herm}_1=1$，只有上述零或秩一情形；
当 $n=2$ 时参考空间实维为四，秩的全部可能值为 $0,1,2,3,4$，本定理正好
覆盖前两种非平凡值。

De las Cuevas--Drescher--Netzer，[*Separability for mixed states with operator
Schmidt rank two*, arXiv:1903.05373v4][T136CDN] 定理1的前件明确是普通
$\rho\succeq0$，结论是其二项算子 Schmidt 分解可改写为两个局部 PSD 因子。
本证明不把该普通 PSD 前件从 $H\in A_n$ 偷换得到；真正的原源增量是
(136.3)、原 $b(H,L)=\operatorname{Tr}(H^TL)$ 极性和(136.5)--(136.8)先行给出
普通 PSD 及其源成员。上述秩是收缩秩，允许 $H$ 在进入时为混合锥元素；
它也不同于134.3已经处理的普通矩阵秩一 dyad。

### 136.C 原 IX132.3 负见证的精确限制

**推论 136.3（原规范负见证只剩秩三或四）。** 固定132.1的任意合法
$y,z,Y,W$，其中量子尺寸 $\ell,m$ 任意有限且所有原旁观、源中间次数、相位、
码、真零扩张和 proper 预算均按132.1保留，令 $q$ 为132.3的原压缩，
$H=qx\in C_2$。若存在普通效应 $F\succeq0$ 使

$$
 \operatorname{Tr}\!\left(F^T M^0_{Y,W}(x,y,z)\right)<0,
\tag{136.10}
$$

则

$$
 r(qx)\in\{3,4\}.
\tag{136.11}
$$

**证明。** 132.3 的源完全正性和规范恒等式说明，若 $H\in B_2$，则规范
输出为 PSD，不能满足(136.10)。所以 $H\notin B_2$。另一方面
$C_2\subseteq A_2$，定理136.2排除 $r(H)\le2$，得到 $r(H)\ge3$。
因为 $\operatorname{Herm}_2$ 的实维为四，$r(H)\le4$，即得(136.11)。
这只是一条必要的秩限制；它不断言秩三或秩四见证存在、输出符号、$R3/R4$、
任何全有限 $N$ 结论或 Fusion3/$t=1$ 结论。∎

[T136CDN]: https://arxiv.org/html/1903.05373v4


## 追加锚（本行以下为增补区）

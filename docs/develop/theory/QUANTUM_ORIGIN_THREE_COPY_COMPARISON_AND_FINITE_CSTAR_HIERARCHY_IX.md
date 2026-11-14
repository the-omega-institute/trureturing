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

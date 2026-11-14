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

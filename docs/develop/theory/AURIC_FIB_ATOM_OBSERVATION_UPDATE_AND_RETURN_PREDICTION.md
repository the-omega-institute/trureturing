# Auric FIB-ATOM：观察更新如何暴露隐藏关系

**来源与范围。** 本卷固定读取快照 `adcffe6`，把五模式金字塔的条件切面与原生共享深度返回路径放在同一更新框架中。五模式读者和项目原生读者是两个不同模型；它们共享条件化原则，但不互相转移资源下界。本文是参考理论正文，未宣称 Lean 已验证。

## 1. 金字塔读出与来源纤维

令

$$
\Sigma=\{\mathsf F[\varnothing],\mathsf F[1],\mathsf F[2],\mathsf F[3],\mathsf F[1,3]\},
$$

其中 $x,y,z$ 分别是低端、高端和中间占位，满足

$$
xz=yz=0.
$$

对概率律 $p=(p_0,p_1,p_2,p_3,p_{13})$，记

$$
X=\mathbb E[x],\qquad Y=\mathbb E[y],\qquad Z=\mathbb E[z],\qquad \kappa=\mathbb E[xy].
$$

则

$$
\mathcal P=\{X,Y,Z\ge0:X+Z\le1,\ Y+Z\le1\},
$$

且

$$
\begin{aligned}
p_0&=1-X-Y-Z+\kappa,&p_1&=X-\kappa,\\
p_2&=Z,&p_3&=Y-\kappa,&p_{13}&=\kappa.
\end{aligned}
$$

### theorem 1.1: 三个均值不决定联合参数

**Claim status: open.** 合法补全的联合参数满足

$$
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y),
$$

且一般情况下该区间非退化。一次确定模式、未知模式律与统计摘要是不同对象；金字塔点是读出均值，不是观察者已经取得的完整来源。

## 2. 条件读出的后验切面

### 定义 2.1：明确的条件读口

真实模式 $s\in\Sigma$ 暂不被动作改变。读口结果 $o$ 的似然为

$$
\ell_o(s)=\Pr(o\mid s),\qquad\sum_o\ell_o(s)=1.
$$

结果概率与后验分别为

$$
q_o=\sum_sp_s\ell_o(s),
\qquad
p_s^{\,o}=\frac{p_s\ell_o(s)}{q_o}\quad(q_o>0).
$$

### theorem 2.2: 读取低端后继位置需要联合参数

**Claim status: open.** 读取 $x$ 后，若结果为一，则

$$
\boxed{(X_1,Y_1,Z_1)=\left(1,\frac\kappa X,0\right).}
$$

若结果为零，则

$$
\boxed{(X_0,Y_0,Z_0)=\left(0,\frac{Y-\kappa}{1-X},\frac Z{1-X}\right).}
$$

相应结果概率为 $X$ 与 $1-X$；零分母的情形只在相应结果概率为零时出现，不作除法。

**证明。** 当 $x=1$ 时，排斥迫使 $z=0$，且 $\Pr(y=1\mid x=1)=\mathbb E[xy]/\mathbb E[x]$。当 $x=0$ 时，$\Pr(y=1,x=0)=Y-\kappa$，而 $z=1$ 已保证 $x=0$。证毕。

两个均值相同的来源

$$
p^{(A)}=\tfrac12\delta_{\varnothing}+\tfrac12\delta_{13},
\qquad
p^{(B)}=\tfrac12\delta_1+\tfrac12\delta_3
$$

都给出 $(X,Y,Z)=(1/2,1/2,0)$。读取 $x$ 的结果概率相同，但结果为一后分别变为 $\delta_{13}$ 与 $\delta_1$，结果为零后分别变为 $\delta_{\varnothing}$ 与 $\delta_3$。同一读口和同一结果概率不保证同一后继来源。

## 3. 观察闭包与联合项

令当前保存的函数空间为

$$
\mathcal V_0=\operatorname{span}\{1,x,y,z\}.
$$

### theorem 3.1: 条件更新的乘法闭包判据

**Claim status: open.** 若有限来源上的函数空间 $\mathcal V$ 含常数一，且读口似然 $\ell_o\in\mathcal V$，则仅凭当前函数均值恢复结果后的全部 $\mathcal V$ 均值，当且仅当

$$
\boxed{f\ell_o\in\mathcal V\quad\text{对所有 }f\in\mathcal V.}
$$

**证明。** 后验均值为

$$
\mathbb E[f\mid o]=\frac{\mathbb E[f\ell_o]}{\mathbb E[\ell_o]}.
$$

正向由闭包直接计算。反向若某个乘积不在 $\mathcal V$，有限维线性代数给出两份当前均值相同而该后验分子不同的严格正来源律。证毕。

读取 $x$ 时 $\ell_1=x$，要继续更新 $y$ 必须加入 $xy$。利用

$$
x^2=x,\quad y^2=y,\quad z^2=z,\quad xz=yz=0,
$$

得到

$$
\mathcal V_* =\operatorname{span}\{1,x,y,z,xy\},
$$

它在五模式上已经是全部函数空间。只重复读取 $z$ 时，$\mathcal V_0$ 保持闭合；允许读取两端并预测另一端时，$xy$ 是最小新增关系。

## 4. 读口如何改变独立生成族

上一卷的乘积活动权五模式满足

$$
\Delta=p_0p_{13}-p_1p_3=(1-Z)\kappa-XY=0.
$$

### theorem 4.1: 后验独立性的四角条件

**Claim status: open.** 对严格正的五模式概率和似然，令 $q_o=\sum_sp_s\ell_o(s)$。则

$$
\boxed{
\Delta^{,o}=\frac{p_0p_{13}\ell_0\ell_{13}-p_1p_3\ell_1\ell_3}{q_o^2}.
}
$$

若原来源满足 $\Delta=0$，后验仍满足 $\Delta^{,o}=0$ 当且仅当

$$
\boxed{\ell_0\ell_{13}=\ell_1\ell_3.}
$$

**证明。** 将 $p_s^{,o}=p_s\ell_o(s)/q_o$ 代入四格行列式。证毕。

写成对数对角比

$$
\Theta(p)=\log\frac{p_0p_{13}}{p_1p_3}
$$

则

$$
\boxed{\Theta(p^{\,o})-\Theta(p)=\log\frac{\ell_0\ell_{13}}{\ell_1\ell_3}.}
$$

一个没有显式 $xy$ 项的读口也能产生后验联合项。五模式均匀时，取结果一似然

$$
\ell(s)=\frac{1+x(s)+y(s)}3.
$$

它只含 $1,x,y$，但 $q=3/5$，后验为

$$
p^{,1}=\left(\frac19,\frac29,\frac19,\frac29,\frac39\right),
$$

从而

$$
\Delta^{,1}=\frac1{9}\frac3{9}-\frac2{9}\frac2{9}=-\frac1{81}.
$$

这是一种条件化倾斜，不是新增物理作用力。

## 5. 总协方差与结果间的分离

设 $R=(x,y,z)^{\mathsf T}$，读出结果后的均值与协方差为 $m_o,C_o$，未条件化量为 $m,C$。

### theorem 5.1: 条件协方差分解

**Claim status: open.** 有

$$
\boxed{m=\sum_oq_om_o}
$$

以及

$$
\boxed{
C=\sum_oq_oC_o+\sum_oq_o(m_o-m)(m_o-m)^{\mathsf T}.
}
$$

因此 $C-\mathbb E[C_o]\succeq0$。观察把一部分内部不确定性转化为不同结果间的均值分离；这不要求每次结果都使每个方差或熵单调下降。

读取二值 $x$ 时，若 $0<X<1$，令

$$
c_x=(X(1-X),\ \kappa-XY,\ -XZ)^{\mathsf T}.
$$

则

$$
\boxed{\operatorname{Cov}_o(m_o)=\frac{c_xc_x^{\mathsf T}}{X(1-X)},}
$$

其秩至多一。

## 6. 返回控制点不等于返回知识

### 定义 6.1：历史似然更新

设隐藏来源参数为 $k$，历史 $w$ 的似然为 $L_w(k)>0$。当前后验 $\nu$ 更新为

$$
\nu^w(k)=\frac{\nu(k)L_w(k)}{\sum_j\nu(j)L_w(j)}.
$$

### theorem 6.2: 后验回返不变的充要条件

**Claim status: open.** 若 $\nu$ 在其支撑上严格为正，则

$$
\boxed{\nu^w=\nu\iff L_w(k)\text{ 在该支撑上为常数}.}
$$

**证明。** 由 $\nu^w(k)=\nu(k)$ 逐项除以 $\nu(k)$，得到所有似然相同；反向立即成立。证毕。

所以控制器回到同一节点只描述控制流。只有历史对所有相容来源的似然相同，观察者才回到同一份知识。

## 7. 共享深度返回路径的预测更新

现在单独回到项目原生返回模型。固定全过程共享的深度 $K=k$，令

$$
r_k=\frac{F_{k+1}}{F_{k+3}},
\qquad r_1=\frac13,\quad r_2=\frac25,
\quad r_k\in\left[\frac38,\frac5{13}\right]\ (k\ge3).
$$

取得历史 $h$ 后，后验为

$$
\nu_h(k)=
\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_j\mu(j)r_j^{A(h)}(1-r_j)^{B(h)}}.
$$

所有实际读取的字母，包括拒绝与不完整对中的字母，都进入 $A(h),B(h)$；这些计数是分析量，不是免费运行寄存器。

### theorem 7.1: 返回词使下一字母预测严格上升

**Claim status: open.** 对实际返回词 $w=\beta\alpha$，其似然为 $L_w(k)=r_k(1-r_k)$。令 $m_h=\mathbb E_{\nu_h}[r]$，则

$$
\boxed{
m_{hw}-m_h=
\frac{\operatorname{Cov}_{\nu_h}(r,r(1-r))}
{\mathbb E_{\nu_h}[r(1-r)]}.
}
$$

并且

$$
\boxed{
\frac{\operatorname{Var}_{\nu_h}(r)}{5\,\mathbb E[r(1-r)]}
\le m_{hw}-m_h\le
\frac{\operatorname{Var}_{\nu_h}(r)}{3\,\mathbb E[r(1-r)]}.
}
$$

**证明。** 第一式是按更新后验求均值。取独立同分布的 $r,r'$，有

$$
\operatorname{Cov}(r,r(1-r))
=\frac12\mathbb E[(r-r')^2(1-r-r')].
$$

在 $r,r'\in[1/3,2/5]$ 时，$1/5\le1-r-r'\le1/3$，再用 $\frac12\mathbb E[(r-r')^2]=\operatorname{Var}(r)$。证毕。

只要先验在深度一、二上有正质量，任何有限正概率历史后方差仍正，因此 $m_{hw}>m_h$。控制位置回来了，下一次真实预测却已改变。

两深度的有理简化例为 $r_1=1/3,r_2=2/5$ 各占一半。一次返回使相对权重乘以 $27/25$，所以

$$
m_n=\frac{\frac13+\frac25(27/25)^n}{1+(27/25)^n},
\qquad m_1-m_0=\frac1{780}.
$$

## 8. 预测器必须随真实目标移动

### theorem 8.1: 配置预测移动的三角下界

**Claim status: open.** 设返回前后的完整未来律为 $T_h,T_{hw}$，实际配置解码律为 $D_z,D_{z'}$。令

$$
\mathcal V_h=\mathbb E[\operatorname{TV}(D_z,D_{z'})\mid h,w].
$$

则

$$
\boxed{\mathcal V_h\ge
\operatorname{TV}(T_h,T_{hw})-e_{\mathrm{conf}}(h)-e_{\mathrm{conf}}(hw).}
$$

**证明。** 对每个实际配置使用三角不等式，再按同一实际返回的联合配置律求平均。项目原生条件独立关系保证返回词不会偷偷重加权返回前私人配置。证毕。

因为“下一次读取为 $\alpha$”是完整未来律中的事件，$\operatorname{TV}(T_h,T_{hw})\ge m_{hw}-m_h$。项目原生风险卷的更强必要不等式为

$$
\gamma\le\frac{1183}{121}e+\frac6{11}\mathcal V,
\qquad\gamma>0,
$$

其中 $e$ 是两项配置风险超出各自基准的较大值；本卷不重证它，也不为 $\gamma$ 声称数值化。

## 9. 有限配置不能精确记录无限返回预测

### theorem 9.1: 逐配置零误差需要无界可区分状态

**Claim status: open.** 若历史列 $h_n=h_0(\beta\alpha)^n$ 的目标预测 $m_n$ 两两不同，而观察者只读取有限多个当前实际配置，并要求每个 $h_n$ 后配置误差为零，则这样的观察者不存在。

**证明。** 零配置误差要求每个正概率配置的解码律都等于该历史的完整未来律。不同 $n$ 的下一字母概率不同，同一配置不能出现在两个历史的正概率支持中。前 $N+1$ 个历史需要至少 $N+1$ 个不同配置，$N$ 任意，有限配置不可能。证毕。

该结论只针对逐配置精确预测，不声称所有近似预测都需无限资源，也不把连续配置分布向量当成免费寄存器。完整合同中的配置、表、工作空间、地址、程序选择与持久随机性都属于资源。

## 10. 更新核与动态函数边界

设结果 $o$ 的未归一化更新由非负核 $K_o$ 给出：

$$
\widetilde p^{\,o}=K_op,
\qquad q_o=\mathbf1^{\mathsf T}K_op,
\qquad p^{\,o}=K_op/q_o.
$$

静态只读模型是 $K_o=\operatorname{diag}(\ell_o)$。

### theorem 10.1: 反向读出闭包是充分性判据

**Claim status: open.** 设当前保存的函数空间 $\mathcal V$ 含常数一。要对全部来源律恢复每个结果概率及结果后的全部 $\mathcal V$ 均值，当且仅当

$$
\boxed{K_o^{\mathsf T}\mathcal V\subseteq\mathcal V\quad\text{对所有 }o.}
$$

**证明。** 结果后的分子是 $\mathbb E_p[K_o^{\mathsf T}f]$，正向直接计算；反向若某项不在空间，按有限维分离构造当前读数相同而后继结果不同的两份严格正来源。证毕。

逐轮闭包为

$$
\mathcal V_{n+1}=\operatorname{span}\left(\mathcal V_n\cup\{K_o^{\mathsf T}f:f\in\mathcal V_n\}\right).
$$

五模式的五维函数闭包不能自动成为共享深度、无限历史过程的有限实现。

## 11. 相干后继也需要反向闭包

对量子仪器 $\mathcal J_o$，结果概率和后继态为

$$
q_o=\operatorname{tr}\mathcal J_o(\varrho),
\qquad
\varrho^o=\frac{\mathcal J_o(\varrho)}{q_o}.
$$

若当前保留的可观察量空间为 $\mathcal W$，相应条件是

$$
\boxed{\mathcal J_o^\dagger(\mathcal W)\subseteq\mathcal W.}
$$

仅知道结果概率一般不决定后继态；额外酉操作可以保持结果概率而改变输出状态。比如 $\varrho_\pm=(I\pm Y)/2$ 具有相同的 $X,Z$ 读数，但 $U=e^{-i\pi Z/4}$ 将 $Y$ 送到 $-X$，揭示两态差异。

经典 $\kappa$ 与量子非对角相位不是同一对象，但它们遵循同一观察者纪律：后续操作会读取的关系，不能被当前边界无条件删除。

## 追加锚（本行以下为增补区）

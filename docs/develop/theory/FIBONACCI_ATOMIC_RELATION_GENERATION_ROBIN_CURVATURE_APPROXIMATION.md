# Robin 原曲率的正谱逼近距离与最优单原子

本卷续接 [素数前缀卷](FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_PRIME_PREFIX.md)
§455，保留该卷的编号与引用。

## 456. 原曲率与正 Laplace 族之间的统一三点距离

沿用 §450 的同一原函数
\[
 \Phi(v)=\exp\!\left(\int_0^1\frac{1-e^{-vb}}b\,db\right),
 \qquad B(v)=\Phi''(v).
\tag{PLA.1}
\]
被积函数在 \(b=0\) 取连续延拓值 \(v\)。§450.4 的零点解析展开给出 \(B,B',B''\) 在零点邻域连续，
以及 \(B(0)=1/2\)、\(B'(0)=-1/6\)、\(B''(0)=-1/6\)。
三阶值也直接由原定义的有限积分矩在零点取值
\(1,1/2,1/3\)，通过 \(1-3/2+1/3=-1/6\) 得到。
这些既有同对象求导供应作为下述
距离估计的供应；本节不另行声称经典指数凸性或 Dickman 变换是新结果。

### 456.1 同一正区间上的定量中点缺口

**定理 456.1。** 存在一个固定 \(0<\eta<1\)，使 \(B>0\)、\(B'<0\) 在 \([0,\eta]\) 上成立，
并且对所有 \(0<a<b<\eta\)，置 \(m=(a+b)/2\)，有
\[
 d(a,b):=B(m)-\frac{B(a)+B(b)}2
 \ge \frac{(b-a)^2}{96}>0.
\tag{PLA.2}
\]

**证明。** 由 \(B''(0)=-1/6\) 及连续性，选择一个固定
\(0<\eta<1\)，使 \(B''(v)\le-1/12\) 对全部
\(v\in[0,\eta]\) 成立。进一步缩小同一个 \(\eta\)，由
\(B(0)=1/2\)、\(B'(0)=-1/6\) 及连续性，使该闭区间上
\(B>0\)、\(B'<0\) 同时成立。令 \(H(v)=B(v)+v^2/24\)。则
\(H''(v)=B''(v)+1/12\le0\)，故 \(H\) 在该区间凹。
其经典中点不等式给
\[
 B(m)+\frac{m^2}{24}
 \ge\frac{B(a)+B(b)}2+\frac{a^2+b^2}{48}.
\]
移项并用 \(a^2+b^2-2m^2=(b-a)^2/2\)，即得（PLA.2）。证毕。

### 456.2 任意正测度表示的统一误差下界

**定理 456.2。** 取定理 456.1 的同一个 \(\eta\)。对任意
\(0<a<b<\eta\)、\(m=(a+b)/2\)、\(c>0\) 和实线上的正测度
\(\mu\)，假设三个核 \(t\mapsto e^{-at}\)、\(t\mapsto e^{-mt}\)、
\(t\mapsto e^{-bt}\) 分别对 \(\mu\) 可积，记这三点上的真实积分为
\[
 L_\mu(v)=\int_{\mathbb R}e^{-vt}\,d\mu(t),
 \qquad v\in\{a,m,b\}.
\]
则
\[
 \begin{aligned}
 E(c,\mu;a,b)&:=\max_{v\in\{a,m,b\}}
             |cB(v)-L_\mu(v)|\\
 &\ge\frac{c\,d(a,b)}2
 \ge\frac{c(b-a)^2}{192}.
 \end{aligned}
\tag{PLA.3}
\]
特别地，同一个固定三点组 \(a=\eta/3\)、\(m=\eta/2\)、
\(b=2\eta/3\) 对每个 \(c>0\) 和全部上述正测度同时满足
\[
 E(c,\mu;\eta/3,2\eta/3)\ge\frac{c\eta^2}{1728}>0.
\tag{PLA.4}
\]
不要求 \(\mu(\mathbb R)<\infty\)，也不要求其支撑包含于非负轴。

**证明。** 实指数函数的凸性给每个实数 \(t\) 的点态不等式
\[
 e^{-mt}\le\frac{e^{-at}+e^{-bt}}2.
\]
三个完整可积性假设支付积分比较与线性性，故
\(L_\mu(m)\le[L_\mu(a)+L_\mu(b)]/2\)。记
\(e_v=cB(v)-L_\mu(v)\)。于是
\[
 \begin{aligned}
 c\,d(a,b)
 &=e_m-\frac{e_a+e_b}{2}
   +L_\mu(m)-\frac{L_\mu(a)+L_\mu(b)}2\\
 &\le |e_m|+\frac{|e_a|+|e_b|}{2}
 \le 2E(c,\mu;a,b).
 \end{aligned}
\]
再用（PLA.2）并代入 \(b-a=\eta/3\)，得到全部结论。证毕。

### 456.3 缩小区间时保留的二阶误差

**定理 456.3。** 固定 \(c>0\)。对每个 \(0<h<\eta/2\)，允许
选取不同的正测度 \(\mu_h\)，仅要求三个参数
\(h,3h/2,2h\) 的指数核分别可积。则
\[
 \lim_{h\downarrow0}
 \frac{B(3h/2)-[B(h)+B(2h)]/2}{h^2}=\frac1{48},
 \qquad
 \liminf_{h\downarrow0}\frac{E(c,\mu_h;h,2h)}{h^2}
 \ge\frac{c}{96}.
\tag{PLA.5}
\]
第二个下极限允许取扩展实值；没有对模型随 \(h\) 的选择加连续性限制。

**证明。** 由原 \(B\) 在零点的二阶可微性，经典 Taylor 展开给
\[
 B(v)=B(0)+B'(0)v+\tfrac12B''(0)v^2+o(v^2).
\]
在三个参数处相减，常数项与一次项完全消去，二次系数为
\[
 \frac12B''(0)\left(\frac94-\frac{1+4}{2}\right)
 =-\frac18B''(0)=\frac1{48}.
\]
三个余项各自为 \(o(h^2)\)，故得第一个极限。定理 456.2 的
第一重不等式对每个 \(\mu_h\) 分别成立，除以 \(h^2\) 后取下极限
得到第二个结论。证毕。

（PLA.5）是正 Laplace 逼近族必须支付的下界，未断言 \(c/96\)
是该族可达到的最优常数。对一般中点凸三点数据，（PLA.3）中的
\(d/2\) 不能仅由中点凸性改进：把原两端值的仿射插值整体上移
\(d/2\)，三个点的误差恰好都是 \(d/2\)。该仿射函数未被断言为
正 Laplace 变换。

### 456.4 正 Laplace 族的精确最优三点距离

**定理 456.4。** 对定理 456.1 的同一个区间及任意
\(0<a<b<\eta\)、\(m=(a+b)/2\)、\(c>0\)，置
\[
 x=cB(a),\qquad y=cB(m),\qquad z=cB(b),\qquad
 K=\frac{y^2-xz}{2y+x+z}.
\tag{PLA.6}
\]
则 \(0<K<y\)。全部满足定理 456.2 三核可积性假设的实线正测度，
其三点误差均满足 \(E(c,\mu;a,b)\ge K\)。该下界由一个位于
严格正位置的单正原子精确达到。因此它也是把测度支撑限制在
\([0,\infty)\) 后的精确最小值。此外
\[
 K=\frac{c\,d(a,b)}2+
   \frac{(x-z)^2}{4(2y+x+z)}
 >\frac{c\,d(a,b)}2.
\tag{PLA.7}
\]

**证明。** \(B\) 在所选区间严格正且严格递减，故 \(x>z>0\)、
\(y>0\)。严格中点缺口给 \(y>(x+z)/2\ge\sqrt{xz}\)，所以
\(K>0\)。直接代数运算给
\[
 y-K=\frac{(y+x)(y+z)}{2y+x+z}>0,
 \qquad (y-K)^2=(x+K)(z+K).
\tag{PLA.8}
\]
这也证明 \(K<y\)。

对任意所述正测度，经典积分 Cauchy--Schwarz 不等式应用于
\(e^{-at/2}\)、\(e^{-bt/2}\)。它们的平方积分恰是已经有限的
\(L_\mu(a)\)、\(L_\mu(b)\)，乘积是中点核，故完整合法地得到
\[
 L_\mu(m)^2\le L_\mu(a)L_\mu(b).
\]
记 \(E=E(c,\mu;a,b)\)。若 \(E\ge y\)，则已经有 \(E>K\)。
若 \(E<y\)，三个积分非负，并且
\[
 0<y-E\le L_\mu(m),\quad
 L_\mu(a)\le x+E,\quad L_\mu(b)\le z+E.
\]
因此
\[
 (y-E)^2\le (x+E)(z+E),
 \qquad y^2-xz\le(2y+x+z)E,
\]
从而 \(E\ge K\)。这证明了全体正测度的下界，没有对未知测度求导。

令
\[
 \tau=\frac{\log((x+K)/(z+K))}{b-a}>0,
 \qquad w=(x+K)e^{a\tau}>0,
\]
并取质量为 \(w\)、位置为 \(\tau\) 的单点正测度
\(\mu_*=w\delta_\tau\)。它的指数核对每个实参数都真正可积，且
\[
 L_{\mu_*}(a)=x+K,\quad L_{\mu_*}(b)=z+K,\quad
 L_{\mu_*}(m)=\sqrt{(x+K)(z+K)}=y-K.
\]
故三个点的绝对误差恰好都是 \(K\)，实现最小值；\(\tau>0\)
同时支付非负支撑的限制。

最后，把 \(y^2-xz\) 写成
\([y-(x+z)/2][y+(x+z)/2]+(x-z)^2/4\)，除以
\(2y+x+z=2[y+(x+z)/2]\)，即得（PLA.7）。证毕。

**推论 456.4.1。** 固定 \(c>0\)，在 \(a=h\)、\(b=2h\) 的区间族上，
上述正 Laplace 族的精确最小误差 \(K_h\) 满足
\[
 \lim_{h\downarrow0}\frac{K_h}{h^2}=\frac{c}{72}.
\tag{PLA.9}
\]
因此定理 456.3 中任意随 \(h\) 改变的可积正测度族，实际满足更强的
\(\liminf E(c,\mu_h;h,2h)/h^2\ge c/72\)。

**证明。** 由（PLA.5），（PLA.7）的第一项除以 \(h^2\) 后趋于
\(c/96\)。一阶 Taylor 公式及 \(B'(0)=-1/6\) 给
\(x_h-z_h=ch/6+o(h)\)，而
\(2y_h+x_h+z_h\to4cB(0)=2c\)。故第二项除以 \(h^2\) 后趋于
\(c/288\)。两项相加即 \(c/72\)；最小误差的下界又逐点约束任何
测度族。证毕。

### 456.5 正混合与极限不能消除同一缺口

**定理 456.5。** 固定定理 456.1 中的一对 \(a,b\) 及其中点 \(m\)。
从实指数核 \(v\mapsto e^{-vt}\) 出发，任意层数的有限非负线性组合，
以及这些组合在 \(a,m,b\) 三点均有有限值的逐点极限，都满足
\(g(m)\le[g(a)+g(b)]/2\)。因此将（PLA.3）中的 \(L_\mu\) 换成
任何这样的 \(g\)，同样有
\[
 \max_{v\in\{a,m,b\}}|cB(v)-g(v)|
 \ge\frac{c\,d(a,b)}2\ge\frac{c(b-a)^2}{192}.
\tag{PLA.10}
\]
特别地，在固定含有这三个点的紧区间上，不存在由此类正组合形成的
序列一致收敛到 \(cB\)。

**证明。** 每个指数核满足中点不等式，非负加权与有限求和保持该
不等式，故归纳给出任意有限层数。三个有限实极限保持同一非严格
不等式。定理 456.2 的误差推导只用了这一中点不等式，因而仍成立。
若存在所述一致收敛，三点最大误差会趋于零，与固定严格正下界矛盾。
证毕。

§450 中曲率密度的正性和完整概率归一化与这些结论相容。它们没有把
实际 Möbius 有符号权重变为非负权重，也没有给出 Robin 临界前段或
互补尾的下界。新的统一三点距离、精确最优单原子和二阶最小误差为上述同对象
推导；指数凸性、可积函数的积分线性性、积分 Cauchy--Schwarz、
Taylor 公式及极限保序均复用经典供应。

## 457. 原曲率的全区间正 Laplace 最优逼近与临界窗口

保持 §450、§456 的同一个原函数
\[
\Phi(v)=\exp\!\left(\int_0^1\frac{1-e^{-vt}}t\,dt\right),
\qquad B(v)=\Phi''(v).
\tag{UI.1}
\]
零点有限积分与解析展开给
\(B(0)=1/2\)、\(B'(0)=B''(0)=-1/6\)。
取 §456 的同一个固定 \(\eta>0\)，使
\[
B>0,\qquad B'<0,\qquad B''\le-1/12
\quad\text{在 }[0,\eta]\text{ 上成立}.
\tag{UI.2}
\]
固定 \(c>0\)，记 \(F=cB\)。以下全部区间满足 \(0<a<b<\eta\)；
\(c\) 不随区间或后来引入的 \(x\) 改变。

### 457.1 两端可积性支付整个闭区间

令 \(\mathfrak M(a,b)\) 为实线上的正 Borel 测度，要求两个核
\(t\mapsto e^{-at}\)、\(t\mapsto e^{-bt}\) 可积。
不添加总质量有限或 \(\sigma\)-有限假设。
对 \(\mu\in\mathfrak M(a,b)\)，置
\[
L_\mu(v)=\int_{\mathbb R}e^{-vt}\,d\mu(t),\quad
E_{[a,b]}(\mu)=\sup_{v\in[a,b]}|F(v)-L_\mu(v)|.
\tag{UI.3}
\]

**引理 457.1。** 两端可积性使 \(L_\mu\) 在整个 \([a,b]\) 上有限且连续。
若 \(\theta=(v-a)/(b-a)\)，则
\[
L_\mu(v)\le L_\mu(a)^{1-\theta}L_\mu(b)^\theta
\quad(0<\theta<1).
\tag{UI.4}
\]

**证明。** 点态加权算术—几何不等式给
\[
e^{-vt}=(e^{-at})^{1-\theta}(e^{-bt})^\theta
\le(1-\theta)e^{-at}+\theta e^{-bt}
\le e^{-at}+e^{-bt}.
\]
右侧是整个闭区间共同的可积主导。参数逐点连续，故支配收敛
支付 \(L_\mu\) 的连续性，包括两端；有限性也由同一个主导得到。
因此（UI.3）的上确界是有限的，且在紧区间上取到。

若一个端点积分为零，则严格正的端点核使 \(\mu\) 为零测度：
集合 \(\{t:e^{-at}\ge1/n\}\) 遍历实线，零积分令其测度均为零；
另一端同理。（UI.4）在零测度情形显然成立。
否则记 \(A_\mu=L_\mu(a)>0\)、\(C_\mu=L_\mu(b)>0\)，
并应用点态加权算术—几何不等式于
\[
p(t)=e^{-at}/A_\mu,\qquad q(t)=e^{-bt}/C_\mu.
\]
两者的积分均为 1，所以
\[
\frac{L_\mu(v)}{A_\mu^{1-\theta}C_\mu^\theta}
=\int p^{1-\theta}q^\theta\,d\mu
\le\int[(1-\theta)p+\theta q]\,d\mu=1.
\]
这给（UI.4），并直接支付其积分合法性，无需对未知测度的
Laplace 变换求导。证毕。

### 457.2 唯一标量根与内部交替误差

对 \(E\ge0\)，定义
\[
\begin{aligned}
G_E(v)&=(F(a)+E)^{1-\theta}(F(b)+E)^\theta,
\qquad \theta=\frac{v-a}{b-a},\\
\tau_E&=\frac{\log((F(a)+E)/(F(b)+E))}{b-a}>0,\\
G_E(v)&=(F(a)+E)e^{-\tau_E(v-a)},\\
D_E(v)&=F(v)-G_E(v),\\
H(E)&=\max_{v\in[a,b]}D_E(v)-E.
\end{aligned}
\tag{UI.5}
\]
这些正端点保证所有幂、对数及指数均有定义。

**引理 457.2。** \(H\) 在 \([0,\infty)\) 上连续且严格递减，
\(H(0)>0\)，并最终为负。故有唯一正根 \(E_*=E_*(c;a,b)\)。
对每个 \(E\ge0\)，\(D_E\) 的最小值在两端取到且恰为 \(-E\)，
最大值在唯一的 \(v_E\in(a,b)\) 取到。
特别地，\(v_*=v_{E_*}\) 满足
\[
D_{E_*}(a)=D_{E_*}(b)=-E_*,
\qquad D_{E_*}(v_*)=E_*,
\qquad F'(v_*)+\tau_{E_*}G_{E_*}(v_*)=0.
\tag{UI.6}
\]

**证明。** 因 \(F(a)>F(b)>0\)，\(\tau_E>0\)。
在整个区间上
\[
D_E''(v)=F''(v)-\tau_E^2G_E(v)<0.
\]
两端值均为 \(-E\)。严格凹性使全部内部值大于 \(-E\)，
故最小值恰在两端。连续性与紧致性给最大值；
它严格大于两端值，因而在内部，严格凹性又保证该点唯一。
其导数为零给（UI.6）的最后一个方程。

在任意固定有限 \(0\le E\le M\) 上，\(G_E(v)\)
关于 \((E,v)\) 联合连续，且域 \([0,M]\times[a,b]\) 紧致。
因此 \(E'\to E\) 时
\(\sup_v|G_{E'}(v)-G_E(v)|\to0\)；
两个最大值之差不超过这个上确界。这证明 \(H\) 的连续性，
没有把逐点连续误作最大值的连续。

若 \(E_2>E_1\)，两个正端点均增大，所以
\(G_{E_2}(v)\ge G_{E_1}(v)\) 对全部 \(v\) 成立。于是
\[
H(E_2)\le H(E_1)-(E_2-E_1)<H(E_1).
\]
严格凹性和加权算术—几何不等式给每个内部点的
\[
F(v)>(1-\theta)F(a)+\theta F(b)\ge G_0(v),
\]
所以 \(H(0)>0\)。
又 \(F(v)\le F(a)\)、\(G_E(v)\ge F(b)+E\)，从而
\[
H(E)\le F(a)-F(b)-2E\longrightarrow-\infty.
\]
介值定理和严格递减性给唯一正根。根处的最大值为 \(E_*\)，
得到（UI.6）的其余方程。证毕。

### 457.3 全体正测度的精确最小值与唯一最优原子

**定理 457.3。** 全区间正 Laplace 最优误差为
\[
\boxed{\mathcal E_c(a,b):=
\min_{\mu\in\mathfrak M(a,b)}E_{[a,b]}(\mu)
=E_*(c;a,b).}
\tag{UI.7}
\]
其唯一最优测度是严格正位置上的单正原子
\[
\boxed{\mu_*=
(F(a)+E_*)e^{a\tau_*}\delta_{\tau_*},
\qquad \tau_*=\tau_{E_*}>0.}
\tag{UI.8}
\]
因此把测度支持限制到 \([0,\infty)\) 后，精确最小值及最优测度
保持相同。固定端点与唯一内部点的方程（UI.6），连同（UI.5），
精确描述误差 \(-E_*,+E_*,-E_*\) 的交替达到。

**证明：任意正测度的下界与达到性。**
令 \(E=E_{[a,b]}(\mu)\)。两端误差给
\(L_\mu(a)\le F(a)+E\)、\(L_\mu(b)\le F(b)+E\)。
引理 457.1 在内部给 \(L_\mu(v)\le G_E(v)\)，
两端也成立。因此
\[
F(v)-G_E(v)\le F(v)-L_\mu(v)\le E\quad(v\in[a,b]),
\]
即 \(H(E)\le0\)。由引理 457.2，必有 \(E\ge E_*\)。

（UI.8）是有限正原子，其核在每个实参数处均可积，并且
\(L_{\mu_*}=G_{E_*}\)。引理 457.2 已付最小误差 \(-E_*\)
及最大误差 \(+E_*\)，故其整个区间的绝对误差恰为 \(E_*\)。
这证明（UI.7）和非负支持的结论。

**证明：测度本身的唯一性。**
设 \(E_{[a,b]}(\mu)=E_*\)。在唯一内部点 \(v_*\)，
\[
0<G_{E_*}(v_*)=F(v_*)-E_*
\le L_\mu(v_*)
\le L_\mu(a)^{1-\theta_*}L_\mu(b)^{\theta_*}
\le G_{E_*}(v_*),
\]
其中 \(\theta_*=(v_*-a)/(b-a)\in(0,1)\)。
所有不等式都为等号。几何乘积对每个正端点严格递增，
所以 \(L_\mu(a)=F(a)+E_*>0\)、\(L_\mu(b)=F(b)+E_*>0\)。

使用引理 457.1 的归一函数 \(p,q\)，加权算术—几何缺陷
\[
(1-\theta_*)p+\theta_*q-p^{1-\theta_*}q^{\theta_*}\ge0
\]
可积且积分为零。故缺陷为零 \(\mu\)-几乎处处；
严格的等号条件给 \(p=q\) \(\mu\)-几乎处处。
于是
\[
e^{(b-a)t}=\frac{L_\mu(a)}{L_\mu(b)}
\quad\mu\text{-几乎处处},
\]
指数的单射性使 \(\mu\) 集中在唯一的 \(\tau_*>0\)。
端点积分再给其有限质量
\(\mu(\{\tau_*\})=L_\mu(a)e^{a\tau_*}\)。
因此 \(\mu\) 精确为（UI.8），无需调用变换解析唯一性。证毕。

此处没有把一般的内部点强加为 \((a+b)/2\)。
未知的 \(E_*,v_*\) 由
\[
\begin{cases}
F(v_*)-G_{E_*}(v_*)=E_*,\\
F'(v_*)+\tau_{E_*}G_{E_*}(v_*)=0
\end{cases}
\tag{UI.9}
\]
与固定端点定义共同确定。

### 457.4 三点最优原子的全区间一致渐近

现在取 \(a=h\)、\(b=2h\)、\(0<h<\eta/2\)。
§456（PLA.6–9）给三点 \(h,3h/2,2h\) 的精确最小值 \(K_c(h)\)，
以及达到它的单原子变换 \(L_h\)，满足
\[
F(h)-L_h(h)=F(2h)-L_h(2h)=-K_c(h),\quad
F(3h/2)-L_h(3h/2)=K_c(h),\quad
\frac{K_c(h)}{h^2}\to\kappa:=\frac c{72}.
\tag{UI.10}
\]
这个三点原子尚未被断言为每个 \(h\) 的精确全区间最优原子。

**引理 457.4。** 在全部 \(s\in[1,2]\) 上共同有
\[
\boxed{\frac{F(hs)-L_h(hs)}{h^2}
\longrightarrow
q(s):=\frac c{72}-\frac c9(s-3/2)^2.}
\tag{UI.11}
\]
因而
\[
\boxed{\sup_{v\in[h,2h]}|F(v)-L_h(v)|
=\frac c{72}h^2+o(h^2).}
\tag{UI.12}
\]

**证明。** 三点原子的指数参数是
\[
\tau_h=\frac1h\log
\frac{F(h)+K_c(h)}{F(2h)+K_c(h)},\quad
L_h(hs)=(F(h)+K_c(h))e^{-\tau_hh(s-1)}.
\]
由 \(F(0)=c/2\)、\(F'(0)=-c/6\)、零点二阶 Taylor 公式及
\(K_c(h)=O(h^2)\)，
\[
F(h)+K_c(h)=c/2-ch/6+O(h^2),\quad
F(2h)+K_c(h)=c/2-ch/3+O(h^2).
\]
在固定正邻域上对对数作 Taylor 展开，得到
\(\tau_h=1/3+O(h)\)。
指数参数有界，\(0\le s-1\le1\)，故
\[
L_h(hs)\to c/2
\quad\text{共同于 }s\in[1,2].
\]
令 \(e_h(s)=[F(hs)-L_h(hs)]/h^2\)。原 \(B''\) 的连续性及
上述参数估计使
\[
e_h''(s)=F''(hs)-\tau_h^2L_h(hs)
\longrightarrow-c/6-c/18=-2c/9
\]
共同于整个 \([1,2]\)。
同时由（UI.10），两端 \(e_h(1)=e_h(2)=-K_c(h)/h^2\to-\kappa\)。
\(q''=-2c/9\)、\(q(1)=q(2)=-\kappa\)。

为支付一致余项，置 \(r_h=e_h-q\)、\(\delta_h=\sup|r_h''|\to0\)。
两端余项相同；从 \(r_h\) 减去其端点仿射插值后，
二阶导数的上下界与零端点给
\[
\left|r_h(s)-[(2-s)r_h(1)+(s-1)r_h(2)]\right|
\le\frac{\delta_h}{2}(s-1)(2-s)\le\frac{\delta_h}{8}.
\]
该式可直接由与正负二次函数比较的凸凹性得到。
所以
\[
\sup_{s\in[1,2]}|r_h(s)|
\le|K_c(h)/h^2-\kappa|+\delta_h/8\to0.
\]
这证明（UI.11）。而 \(\sup_{[1,2]}|q|=\kappa\)，
一致范数的三角不等式给（UI.12）。证毕。

**推论 457.4.1。** 全区间的精确最优值同样满足
\[
\boxed{E_h^*:=\mathcal E_c(h,2h)
=\frac c{72}h^2+o(h^2).}
\tag{UI.13}
\]
其唯一内部达到点满足 \(v_h^*/h\to3/2\)。

**证明。** 任意全区间模型的误差不小于三点误差，所以
\(E_h^*\ge K_c(h)\)。三点最优原子是全区间的合法竞争者，
（UI.12）给相同常数的上界；夹逼得到（UI.13）。

将（UI.13）代替（UI.10）中的 \(K_c(h)\)，并使用精确
全区间原子的两个端点值，前述参数与二阶导数论证不变；
归一误差仍一致趋于 \(q\)。\(q\) 在 \([1,2]\) 的最大点
唯一为 \(3/2\)。若归一最大点离它至少一个固定 \(\varepsilon>0\)，
则 \(q\) 的最大值缺额至少 \(c\varepsilon^2/9\)，与一致收敛矛盾。
所以 \(v_h^*/h\to3/2\)。这只是缩小窗口的极限，不把有限
\(h\) 的内部点设为中点。证毕。

### 457.5 全区间最优误差的锐临界窗口

令 \(x\ge e\) 为实数，保持原归一化
\(\mathcal R(x)=\sqrt x\log x\)，定义
\[
h_{\rm crit}(x)=\mathcal R(x)^{-1/2}
=x^{-1/4}(\log x)^{-1/2}.
\]
对任意正函数 \(h(x)\to0\)，（UI.13）给
\[
\boxed{\mathcal R(x)\mathcal E_c(h(x),2h(x))
=\left[\frac c{72}+o(1)\right]
\left(\frac{h(x)}{h_{\rm crit}(x)}\right)^2.}
\tag{UI.14}
\]
这里极限共同覆盖全部充分大实数 \(x\)：先在（UI.13）中选
同一个小 \(h\) 阈值，再使用 \(h(x)\to0\)，无需单调性。
系数最终夹在两个固定正常数之间，故
\[
\mathcal R(x)\mathcal E_c(h(x),2h(x))\to0
\quad\Longleftrightarrow\quad h(x)=o(h_{\rm crit}(x)).
\tag{UI.15}
\]
由定理 457.3 的精确达到性，这也等价于存在一个在每个整个
\([h(x),2h(x)]\) 上误差为 \(o(\mathcal R(x)^{-1})\) 的正
Laplace 模型族。类似地，存在全区间误差
\(O(\mathcal R(x)^{-1})\) 的模型族，当且仅当
\(h(x)=O(h_{\rm crit}(x))\)。
这些存在性不意味着每个模型族都达到最优误差。

固定 \(\rho>0\)、\(b\in\mathbb R\)，取
\(h(x)=x^{-\rho}(\log x)^b\)。因为
\(-\rho\log x+b\log\log x\to-\infty\)，三个节点和整个窗口
最终都留在原正区间。由（UI.13）得到
\[
\boxed{\sqrt x\log x\,\mathcal E_c(h(x),2h(x))
\sim\frac c{72}x^{1/2-2\rho}(\log x)^{1+2b}.}
\tag{UI.16}
\]

| 固定参数范围 | 全区间最优误差的临界归一化极限 |
| --- | --- |
| \(0<\rho<1/4\)，任意固定 \(b\) | \(+\infty\) |
| \(\rho=1/4,\ b>-1/2\) | \(+\infty\) |
| \(\rho=1/4,\ b=-1/2\) | \(c/72>0\) |
| \(\rho=1/4,\ b<-1/2\) | \(0\) |
| \(\rho>1/4\)，任意固定 \(b\) | \(0\) |

分类的证明是对正因子取对数：
\((1/2-2\rho)\log x+(1+2b)\log\log x\)。
非零的第一个系数压过任意固定第二项；第一个系数为零时，
按第二个系数的正、零、负分别得到发散、常数和趋零。
在 \(h=h_{\rm crit}\) 上，任意正模型族的归一化误差下极限
至少 \(c/72\)，而唯一全区间最优原子族的极限恰为 \(c/72\)。
该正储备与允许固定临界常数的误差合同相容。

### 457.6 与来源截止及实际有符号预算的范围

§455 的 \(N\) 是实际整数来源截止，本节的 \(h\) 是曲率参数。
只有在明确选择
\[
h_N(x)=\sqrt{x/(N+1)}
\tag{UI.17}
\]
后，才有下面的共同范数比较。
若 \(a_x=\log((N+1)/x)/\log x\) 留在先固定的正紧区间
\([\alpha,\beta]\)，则 \(h_N\le x^{-\alpha/2}\to0\) 共同成立。
（UI.13）因此给
\[
\sqrt x\log x\,\mathcal E_c(h_N,2h_N)
=\frac{x^{3/2}\log x}{N+1}[c/72+o_{\alpha,\beta,c}(1)].
\tag{UI.18}
\]
共同余项由同一个 \(h\) 阈值与 \(h_N\le x^{-\alpha/2}\) 支付。
§455 的实际面板补偿使用同一外部因子，内核为
\(F_0(a_x)+O_{\alpha,\beta}(1/\log x)\)，其中
\(F_0(a)=(1+a)\log(1+a)-a\)；这区别于本节 \(F=cB\)。

特别地，\(N=\lceil\lambda x^{3/2}\log x\rceil\)、\(\lambda>0\)
给 \(h_N/h_{\rm crit}\to\lambda^{-1/2}\)，故本节的全区间最优误差
临界极限为 \(c/(72\lambda)\)，而原实际面板补偿极限为
\(F_0(1/2)/\lambda\)。
这是选择（UI.17）后的参数比较，不是两种误差的来源身份或保号运输。

本节完整支付的是同一个 \(cB\) 在整个局部区间上的正
Laplace 替代误差。它没有将实际奇 Möbius 系数变为非负系数，
也没有建立从该一致距离到原
\(I_\psi(x)=\sum O(n)\mathcal L_x(n)\) 的误差运输。
实际有限前段、全实际 \(O(N)\mathscr D_x(N+1)\) 边界、
自然奇源余项及精确 \(\mathcal A_x\) 仍须使用其自身的完整来源合同，
保留单位和全部 \(\beta\) 纤维。
若某个步骤要求这份一致替代误差为
\(o(1/(\sqrt x\log x))\)，（UI.15）给它的必要且可达到的窗口条件；
若原 RH 方法不要求这份一致误差，或允许有符号谱和已证明的
积分抵消，不能由本节断言该方法不可行。

原 \(B\)、近零正区间和三点精确最优距离复用 §§450、456。
加权算术—几何不等式、支配收敛、紧区间一致连续性、严格凹性、
介值定理及 Taylor 公式为经典供应。全区间标量根、唯一最优正原子、
一致二阶误差与临界窗口为同对象推导；这些结论不提供原
Robin 有符号下界或 RH。

## 458. 三点与全区间最优原子的四阶分离

沿用 §456–457 的同一 $B=\Phi''$，固定 $c>0$，令 $F=cB$，窗口为
$[h,2h]$，其中 $h\downarrow0$。记 $K_h$ 为 §456.4 的准确三点最优误差，
$E_h$ 为 §457.2 的准确全区间最优根，$v_h$ 为全区间最优原子的唯一内部
正误差最大点。以下所有 $O$ 常数允许依赖固定的 $c$，不依赖 $h$ 或窗口位置。
本节补充实际曲率的局部高阶关系；经典 Taylor 展开和极大值扰动方法是供应。

### 458.1 原有限积分矩与递归零点系数

**引理 458.1。** 原函数在实零点邻域光滑。若 $\beta_n=\Phi^{(n)}(0)$，则

$$
\beta_0=1,\qquad
\beta_{n+1}=\sum_{k=0}^n\binom nk\frac{(-1)^k}{k+1}\beta_{n-k}.
\tag{HO.1}
$$

特别地，$\beta_2=1/2$、$\beta_3=\beta_4=-1/6$、$\beta_5=11/30$，从而

$$
B(v)=\frac12-\frac v6-\frac{v^2}{12}+\frac{11v^3}{180}+O(v^4).
\tag{HO.2}
$$

证明。原 rate 的有限积分表示为
$r(v)=\int_0^1e^{-vb}\,db$。在任意固定紧参数邻域 $|v|\le R$ 上，
第 $k$ 阶核导数为 $(-b)^ke^{-vb}$，绝对值不超过 $e^R$。
有限测度区间上的逐阶积分求导因此支付 $r$ 的所有阶导数，并给
$r^{(k)}(0)=(-1)^k/(k+1)$。原 compensated 积分等于 $\int_0^v r(w)\,dw$，
故 $\Phi'=r\Phi$，逐阶 Leibniz 公式给（HO.1）。按该递推算至 $n=4$，
依次得到 $(1,1,1/2,-1/6,-1/6,11/30)$。光滑性在固定邻域上给所需
有界高阶导数，Taylor 公式得到（HO.2）及其逐阶导数的对应一致余项。

### 458.2 三点原子的误差形状及最大点偏移

令 $a_h=F(h)$、$b_h=F(2h)$、$y_h=F(3h/2)$。三点准确公式为

$$
K_h=\frac{y_h^2-a_hb_h}{2y_h+a_h+b_h},\qquad
\tau_h=\frac1h\log\frac{a_h+K_h}{b_h+K_h}.
\tag{HO.3}
$$

其准确最优变换记为
$L_h(v)=(a_h+K_h)e^{-\tau_h(v-h)}$，误差为 $D_h=F-L_h$。
因此 $D_h(h)=D_h(2h)=-K_h$，$D_h(3h/2)=K_h$ 都是准确等式。

**定理 458.2。** 有

$$
K_h=\frac{c}{72}h^2-\frac{c}{45}h^3+O(h^4).
\tag{HO.4}
$$

对 $s\in[1,2]$，一致于函数及其一阶导数，

$$
\frac{D_h(hs)}{h^2}=q(s)+ch\,p(s)+O_{C^1}(h^2),
\tag{HO.5}
$$

其中

$$
q(s)=\frac c{72}-\frac c9(s-3/2)^2,\qquad
p(s)=\frac{26}{405}s^3-\frac19s^2-\frac{47}{405}s+\frac5{27}.
\tag{HO.6}
$$

三点原子的唯一误差最大点 $w_h$ 及其最大值满足

$$
w_h=\frac32h-\frac{13}{180}h^2+O(h^3),\qquad
\max_{[h,2h]}D_h-K_h=\frac{169c}{291600}h^4+O(h^5).
\tag{HO.7}
$$

证明。将（HO.2）代入（HO.3）。分母为 $2c+O(h)$，有固定正下界，
有限 Taylor 除法合法，得到（HO.4）及
$\tau_h=1/3+(2/3)h+O(h^2)$。后者与端点振幅给
$L_h(hs)=c/2-(c/6)hs+O(h^2)$，一致于整个 $s\in[1,2]$。
因 $D_h''=cB''-\tau_h^2L_h$，进一步得到

$$
D_h''(hs)=-\frac{2c}{9}
 +ch\left(\frac{52}{135}s-\frac29\right)+O(h^2).
\tag{HO.8}
$$

这里余项来自固定紧区间上的有界导数及有正下界的分母，因而确实一致。
令 $e_h(s)=D_h(hs)/h^2$，则 $e_h''(s)=D_h''(hs)$。
（HO.6）的二阶导数恰为（HO.8）的两个显式项；
$p(1)=p(2)=1/45$，而 $q(1)=q(2)=-c/72$。
准确端点数据与（HO.4）给余函数
$R_h=e_h-q-chp$ 的两端值均为 $O(h^2)$，且
$\sup|R_h''|=O(h^2)$。中值定理给某个 $\xi\in(1,2)$ 上
$R_h'(\xi)=R_h(2)-R_h(1)=O(h^2)$；再积分二阶导数，得到
$\sup|R_h'|=O(h^2)$，随后积分一阶导数得到
$\sup|R_h|=O(h^2)$。这支付了（HO.5）的完整 $C^1$ 余项。

直接有 $p'(3/2)=-13/810$。令 $m_h=3h/2$，于是

$$
D_h'(m_h)=-\frac{13c}{810}h^2+O(h^3),\qquad
D_h''(v)=-\frac{2c}{9}+O(h)
\quad(h\le v\le2h).
\tag{HO.9}
$$

对充分小的 $h$，二阶导数统一负且绝对值远离零；（HO.5）的导数在
两端分别正、负。因此有唯一内部极大点 $w_h$。中值定理先给
$|w_h-m_h|=O(h^2)$，再将（HO.9）代入驻点等式，给（HO.7）的偏移。
在 $m_h$ 与 $w_h$ 之间使用二阶 Taylor 公式，记 $d_h=w_h-m_h$，则

$$
D_h(w_h)-D_h(m_h)
=D_h'(m_h)d_h+\frac12D_h''(\zeta_h)d_h^2
=\frac{169c}{291600}h^4+O(h^5).
\tag{HO.10}
$$

最后使用准确等式 $D_h(m_h)=K_h$。因此（HO.10）没有相减两份
未知的四阶 Taylor 余项。

### 458.3 全区间最优根的四阶修正

**定理 458.3。** 原全区间最优误差和唯一内部最大点满足

$$
E_h-K_h=\frac{169c}{583200}h^4+O(h^5),\qquad
v_h=\frac32h-\frac{13}{180}h^2+O(h^3).
\tag{HO.11}
$$

故在全部充分小的正 $h$ 上，$E_h>K_h$，而

$$
E_h=\frac c{72}h^2-\frac c{45}h^3+O(h^4).
\tag{HO.12}
$$

证明。记 $\theta=(v-h)/h$、$U=a_h+E$、$V=b_h+E$，并沿用
$G_E(v)=U^{1-\theta}V^\theta$ 和
$H_h(E)=\max_{[h,2h]}(F-G_E)-E$。由准确三点数据，
$G_{K_h}=L_h$，因此（HO.10）给

$$
H_h(K_h)=\frac{169c}{291600}h^4+O(h^5).
\tag{HO.13}
$$

全区间族包含三点的约束，故 $E_h\ge K_h$。亦可直接由（HO.13）的
严格正性及 $H_h$ 严格下降性取得充分小 $h$ 时的严格不等式。
由于 $G_E$ 随 $E$ 递增，任意 $E_2\ge E_1$ 有
$H_h(E_2)\le H_h(E_1)-(E_2-E_1)$。在准确根 $H_h(E_h)=0$ 处，
这先给 $\delta_h:=E_h-K_h=O(h^4)$，而非预先假设它的阶。

现在 $E\in[K_h,E_h]$ 上有 $E=O(h^2)$，且 $U,V=c/2+O(h)$，
所以两者均有固定正下界。直接求导得

$$
\partial_EG_E(v)=G_E(v)
 \left(\frac{1-\theta}{U}+\frac\theta V\right)=1+O(h^2),
\tag{HO.14}
$$

一致于 $0\le\theta\le1$ 与整个上述参数区间。为核对余项，令
$r=V/U=1+O(h)$；左式成为
$r^\theta[(1-\theta)+\theta/r]$。它在 $r=1$ 的值为 $1$，
一阶 $r$ 导数为零，其二阶导数在 $\theta\in[0,1]$、
$r$ 的固定正紧邻域上一致有界。Taylor 公式因此给（HO.14），
无需对依赖 $h$ 的极大点求导。

将（HO.14）对 $E$ 积分，并用
$|\max f-\max g|\le\|f-g\|_\infty$，可得

$$
0=H_h(E_h)=H_h(K_h)-2\delta_h+O(h^2\delta_h).
\tag{HO.15}
$$

结合（HO.13）及 $\delta_h=O(h^4)$，便得（HO.11）的四阶差值。

最后 $G_E'=-\tau_EG_E$，其中
$\tau_E=h^{-1}\log(U/V)$。在同一参数区间上
$\tau_E=O(1)$ 且
$\partial_E\tau_E=h^{-1}(1/U-1/V)=O(1)$，因此
$\partial_EG_E'=O(1)$ 一致成立。于是
$\|G_{E_h}'-G_{K_h}'\|_\infty=O(h^4)$。
实际 $B''$ 的统一负下界和 $G_E''\ge0$ 保证 $F-G_E$ 的二阶导数
统一负且远离零；比较两者的唯一驻点得到
$v_h-w_h=O(h^4)$。代入（HO.7）给（HO.11）的最大点展开。

### 458.4 递归与临界分类的关系

（HO.1）的递推由同一个有限指数核产生，不引入新的数论假设。
它把局部导数信息运输到（HO.5）的误差形状，再通过准确标量根
运输到全区间最优值。三点约束捕捉二阶储备及三次修正；
整段约束在四阶才支付最大点偏移的额外误差。
因此 §457.5 的五种临界尺度分类保持原首项，仍可在每个类别内部
比较更精细的误差和原子位置。这是同一最优问题内部的关系，
不是 Fibonacci 递推、整数 $5040$ 或拓扑例外与该解析递推的等价证明。

本节为上述同对象逼近问题的普通数学推导；Taylor、Leibniz 和
极大值稳定性的方法不作新颖性主张。这里没有提供实际 Möbius 权重的
有符号前段下界、相应运输估计或 RH 证明，也没有声称这些高阶结果已形式化。

## 追加锚（本行以下为增补区）

## 459. 原曲率三点逼近的精确负质量、谱率逃逸与实际 Möbius 配对边界

本节保持 §§450、456–457 的实际曲率
$$
\Phi(v)=\exp\!\left(\int_0^1\frac{1-e^{-vt}}t\,dt\right),
\qquad B(v)=\Phi''(v).
$$
对于这一原函数，非负谱率上的三个实际节点具有精确的允许误差与最小原始负质量关系，
最优测度只含一个正原子和一个负原子。全实谱率没有同类无支持约束的正负质量下界；
下文给出精确拟合且负质量趋零的构造，并保持实际有限奇 Möbius 阶乘配对的全部来源。

### 459.1 原对象与既有供应

§§456–457 已支付正测度的精确三点距离与全区间最优逼近；
§448 的真实 $e_6>0$ 支付实际密度的非完全单调性，
§455.6 支付原实际有限配对与完整余项的精确关系。
有限 Euler 展开沿用 §§433–435 的同一实际 primorial 对象。
下面求取同一实际曲率的最小负质量。

复用实际值
$$
B(0)=\frac12,\qquad B'(0)=B''(0)=-\frac16,
$$
并复用一个固定 $\eta>0$，使 $B>0$、$B'<0$、$B''<0$
在 $[0,\eta]$ 上同时成立。以下固定 $c>0$。对于
$0<h<\eta/2$，记
$$
u=cB(h),\qquad v=cB(3h/2),\qquad z=cB(2h),
\quad S=2v+u+z,
\quad \Delta=v^2-uz>0,
\quad K=\frac{\Delta}{S}.
\tag{SNC.1}
$$
因此 $u>v>z>0$，且 §456.4 给 $K$ 为正谱精确最小三点误差，
$$
K/h^2\longrightarrow c/72.
\tag{SNC.2}
$$
本节的 signed 记号 $\sigma$ 与算术 Möbius 函数 $\mu$ 严格区分。

### 459.2 非负谱率上的精确负质量问题

对 $[0,\infty)$ 上任意有限实有符号 Borel 测度 $\sigma$，取其真实
Jordan 分解 $\sigma=\sigma^+-\sigma^-$，定义
$$
L_\sigma(s)=\int e^{-st}\,d\sigma(t),\qquad
N_-(\sigma)=\sigma^-([0,\infty)),
$$
$$
E_h(\sigma)=\max_{s\in\{h,3h/2,2h\}}|cB(s)-L_\sigma(s)|.
\tag{SNC.3}
$$
这里每个核在非负轴有界，故三核对总变差都真正可积。
成本始终是 Jordan 负部的质量；不能用某个含重叠的作者分解代替它。

给定 $0\le\varepsilon\le K$，置
$$
U=u+\varepsilon,\qquad V=v-\varepsilon,\qquad Z=z+\varepsilon,
\qquad \Delta_\varepsilon=V^2-UZ=\Delta-S\varepsilon
 =S(K-\varepsilon)\ge0,
\tag{SNC.4}
$$
$$
D_\varepsilon=\sqrt{9V^2-8UZ}
 =\sqrt{V^2+8\Delta_\varepsilon},\qquad
r_\varepsilon=\frac{3V-D_\varepsilon}{2U},
$$
$$
n_\varepsilon=\frac{8(V-Ur_\varepsilon)}{r_\varepsilon^3},
\qquad W_\varepsilon=\frac U{r_\varepsilon^2}+\frac{n_\varepsilon}4.
\tag{SNC.5}
$$
由 $K<v$，有 $V>0$；由 $UZ>0$，有 $D_\varepsilon<3V$。
又有 $D_\varepsilon\ge V$，因此
$$
0<r_\varepsilon\le V/U<1,
\quad n_\varepsilon\ge0,\quad W_\varepsilon>0.
\tag{SNC.6}
$$
$n_\varepsilon=0$ 恰当且仅当 $\varepsilon=K$。

**引理 459.1（统一小窗口域）。** 存在仅依赖 $c,B$ 的固定
$0<h_0<\eta/2$，使所有 $0<h<h_0$ 与所有
$0\le\varepsilon\le K_h$ 同时满足
$$
r_*:=2(\sqrt2-1)<r_\varepsilon<1.
\tag{SNC.7}
$$

**证明。** $K_h=O(h^2)$，故 $U,V,Z\to c/2$ 对整个
$\varepsilon\in[0,K_h]$ 一致成立，$\Delta_\varepsilon=O(h^2)$
也一致成立。（SNC.5）的连续公式由正分母支付，所以
$r_\varepsilon\to1$ 一致成立。由于 $r_*<1$，可选共同
$h_0$ 使下界成立，上界已经由（SNC.6）逐点支付。证毕。

**定理 459.2（精确允许误差—负质量关系）。** 对上述同一个 $h_0$，
任意 $0<h<h_0$ 的真实三点数据均满足
$$
\inf_{\substack{\sigma\text{ finite signed on }[0,\infty)\\
                       E_h(\sigma)\le\varepsilon}}
N_-(\sigma)
=
\begin{cases}
n_\varepsilon,&0\le\varepsilon\le K_h,\\
0,&\varepsilon\ge K_h.
\end{cases}
\tag{SNC.8}
$$
当 $0\le\varepsilon\le K_h$ 时，此最小值由唯一测度达到：
$$
t_+=-\frac2h\log r_\varepsilon>0,
\qquad t_-=t_++\frac{2\log2}h>t_+,
$$
$$
\boxed{\quad\sigma_\varepsilon
=W_\varepsilon\delta_{t_+}-n_\varepsilon\delta_{t_-}.\quad}
\tag{SNC.9}
$$
在 $\varepsilon=K_h$ 时，负原子系数精确为零，式（SNC.9）是单正原子。

**证明：全体 signed 测度的下界。** 暂记 $r=r_\varepsilon$，
令 $y=e^{-ht/2}\in(0,1]$。真正的三核非负见证为
$$
q_r(t)=e^{-2ht}-2r e^{-3ht/2}+r^2e^{-ht}
      =y^2(y-r)^2\ge0.
\tag{SNC.10}
$$
对 $0<r<1$，有限闭区间的微分检查给
$$
\sup_{t\ge0}q_r(t)
=\max\{r^4/16,(1-r)^2\}.
\tag{SNC.11}
$$
具体地，$y^2(y-r)^2$ 的导数为
$2y(y-r)(2y-r)$；只需比较 $y=0,r/2,r,1$。
$r>r_*$ 恰好保证 $r^2/4>1-r$，故同一域内
$$
0\le q_r(t)\le M_r:=r^4/16,
$$
且最大值只在 $y=r/2$ 达到，零值在有限谱率上只在 $y=r$ 达到。
$y=0$ 对应无穷谱率，不是实轴上的另一个原子。

（SNC.5）给
$$
Ur^2-3Vr+2Z=0,
\qquad Z-2rV+r^2U=-\frac{n_\varepsilon r^4}{16}
 =-M_r n_\varepsilon.
\tag{SNC.12}
$$
若 $E_h(\sigma)\le\varepsilon$，三个线性系数的真实符号给
$$
\begin{aligned}
\int q_r\,d\sigma
&=L_\sigma(2h)-2rL_\sigma(3h/2)+r^2L_\sigma(h)\\
&\le(z+\varepsilon)-2r(v-\varepsilon)+r^2(u+\varepsilon)\\
&=-M_r n_\varepsilon.
\end{aligned}
\tag{SNC.13}
$$
这里误差盒上的精确最大点是 $(U,V,Z)=(u+\varepsilon,v-\varepsilon,z+\varepsilon)$，
并未把三个误差的同号当成额外假设。
另一方面，真实 Jordan 分解和（SNC.11）给
$$
\int q_r\,d\sigma
=\int q_r\,d\sigma^+-\int q_r\,d\sigma^-
\ge-M_rN_-(\sigma).
\tag{SNC.14}
$$
因此 $N_-(\sigma)\ge n_\varepsilon$。

**证明：真正达到与唯一性。** 两个位置不同，$W_\varepsilon>0$、
$n_\varepsilon\ge0$，所以（SNC.9）本身就是其 Jordan 分解。
正原子的 $y$ 值为 $r$，负原子的值为 $r/2$。于是
$$
\begin{aligned}
L_{\sigma_\varepsilon}(h)&=r^2(W_\varepsilon-n_\varepsilon/4)=U,\\
L_{\sigma_\varepsilon}(3h/2)&=r^3(W_\varepsilon-n_\varepsilon/8)=V,\\
L_{\sigma_\varepsilon}(2h)&=r^4(W_\varepsilon-n_\varepsilon/16)=Z.
\end{aligned}
\tag{SNC.15}
$$
第一、二行直接由定义得到；第三行由（SNC.12）的二次方程得到。
所以其三点最大误差恰好为 $\varepsilon$，负质量恰好为 $n_\varepsilon$。

若任一候选达到此最小值，（SNC.13）–（SNC.14）的全部不等式必须等号。
非负积分的零值迫使 $\sigma^+$ 支撑在 $q_r=0$，
$\int(M_r-q_r)d\sigma^-=0$ 迫使 $\sigma^-$ 支撑在 $q_r=M_r$。
上述真实有限谱率零点与唯一最大点分别是 $t_+$、$t_-$。
三个误差系数严格不为零，误差盒的等号还迫使真实节点值为 $U,V,Z$，
从而两个原子质量由（SNC.15）唯一确定。
此论证也适用于 $n_\varepsilon=0$：Jordan 负部质量零给正测度，
其正部仍只在 $t_+$，质量唯一。
对于 $\varepsilon>K_h$，$\sigma_{K_h}$ 已有误差 $K_h$、负质量零；
成本非负给（SNC.8）的余下范围。证毕。

**全实正部的扩展。** 定理 459.2 的同一结论还适用于实轴上的有限 signed
测度，只要求真实负部支撑在 $[0,\infty)$，并要求三个实际核对总变差可积。
其正部可含任意实谱率：平方核（SNC.10）在全部 $y>0$ 上非负，
而上界 $q_r\le M_r$ 只用于已限制在非负率上的负部。
唯一达到测度仍为（SNC.9）。因此真正承担负质量下界的是负部的位置条件。

### 459.3 一致二阶常数与负谱必须支付的尺度

**推论 459.3。** 在全部 $0\le\varepsilon\le K_h$ 上，有精确乘法式
$$
n_\varepsilon=A_{h,\varepsilon}(K_h-\varepsilon),\qquad
A_{h,\varepsilon}
=\frac{32S_h}{r_\varepsilon^3(D_\varepsilon+V)},
$$
$$
\sup_{0\le\varepsilon\le K_h}|A_{h,\varepsilon}-64|
\longrightarrow0.
\tag{SNC.16}
$$
在 $\varepsilon=K_h$ 时，此式仍给精确零，不作 $0/0$ 比值。
特别地，精确拟合的最小负质量满足
$$
\boxed{\quad n_0/h^2\longrightarrow8c/9.\quad}
\tag{SNC.17}
$$
若 $\varepsilon_h\ge0$ 且 $\varepsilon_h/h^2\to\kappa\in[0,\infty)$，则整个允许误差类的
最小负质量满足
$$
\frac{\inf_{E_h(\sigma)\le\varepsilon_h}N_-(\sigma)}{h^2}
\longrightarrow\bigl(8c/9-64\kappa\bigr)_+.
\tag{SNC.18}
$$
因此任何误差 $o(h^2)$ 的非负率 signed 候选，都有
$\liminf N_-(\sigma_h)/h^2\ge8c/9$；这是必要抵消预算，
其三点常数由（SNC.9）真正达到。

**证明。** 从（SNC.5）有
$$
n_\varepsilon
=\frac{4(D_\varepsilon-V)}{r_\varepsilon^3}
=\frac{32\Delta_\varepsilon}
       {r_\varepsilon^3(D_\varepsilon+V)}.
$$
代入（SNC.4）给（SNC.16）的精确式。
同一误差区间内 $S_h\to2c$、$r_\varepsilon\to1$、
$D_\varepsilon+V\to c$ 一致成立，所以乘子一致趋于 $64$。
（SNC.2）给（SNC.17）；对（SNC.8）分别在 $\varepsilon_h\le K_h$
与 $\varepsilon_h>K_h$ 使用正部函数的连续性，得（SNC.18）。证毕。

精确拟合的最优原子还满足
$$
t_+\longrightarrow1/3,\qquad
ht_-\longrightarrow2\log2,\qquad W_0\longrightarrow c/2.
\tag{SNC.19}
$$
事实上 $u=c/2-ch/6+O(h^2)$、$v=c/2-ch/4+O(h^2)$，
$\Delta=O(h^2)$ 给 $r_0=v/u+O(h^2)=1-h/6+O(h^2)$，
于是 $-2\log r_0/h\to1/3$，其余由（SNC.5）、（SNC.9）得到。
最优负谱率随窗口缩小逃到 $1/h$ 尺度，负质量仍为明确的 $h^2$ 量级。

**推论 459.4（有限谱截止的额外必要预算）。** 固定定理 459.2 的小窗口，
若真实负部进一步支撑于 $[0,T]$，则令
$$
M_{h,T,r}:=\max_{0\le t\le T}q_r(t)>0
$$
便有
$$
N_-(\sigma)\ge\frac{n_\varepsilon r_\varepsilon^4}
                       {16M_{h,T,r_\varepsilon}}
\qquad(E_h(\sigma)\le\varepsilon\le K_h).
\tag{SNC.20}
$$
若 $h\downarrow0$、$T_h\to\infty$、$hT_h\to0$，
而实际误差为 $o(h^2)$，则
$$
\boxed{\qquad\liminf_{h\downarrow0}T_h^2N_-(\sigma_h)
\ge2c/9,\qquad N_-(\sigma_h)/h^2\longrightarrow+\infty.\qquad}
\tag{SNC.21}
$$

**证明。** 在（SNC.14）中只需把负部上的核上界改为
$M_{h,T,r}$，即可得到（SNC.20）。该最大值可直接计算：
令 $y_T=e^{-hT/2}$，比较两个端点 $y=y_T,1$，
并在 $y_T\le r/2$ 时额外比较 $y=r/2$ 的值 $r^4/16$；
其余驻点 $y=r$ 只是零值。
由 $0\le\varepsilon\le K_h=O(h^2)$，有
$r_\varepsilon=1-h/6+O(h^2)$ 一致成立。因此在指定截止族上，
$y_T>r_\varepsilon/2$ 最终成立，端点值满足
$$
q_r(0)=(1-r)^2=O(h^2),\qquad
q_r(T)=y_T^2(y_T-r)^2
=\frac{h^2T^2}{4}[1+o(1)].
$$
后一式使用 $y_T=1-hT/2+O((hT)^2)$、$T\to\infty$
及 $hT\to0$；所以 $M_{h,T,r}\sim h^2T^2/4$。
对于误差 $o(h^2)$，（SNC.16）给 $n_\varepsilon\sim8ch^2/9$，
（SNC.20）便给第一个下极限。第二个结论再用 $h^2T^2\to0$。证毕。

（SNC.8）只求三个实际节点的预算。全区间误差 $o(h^2)$ 自动受其必要下界约束，
但本节没有把两原子三点构造声明为全区间的最优负质量解。

### 459.4 全实谱率的斜率中心加权预算与无约束逃逸

现取任意固定 $0<a<b<\eta$，$m=(a+b)/2$、$\delta=(b-a)/2$，
以及真实数据 $u=cB(a),v=cB(m),z=cB(b)$。令
$$
\tau=\frac{\log(u/z)}{2\delta}>0,
\qquad d_G=v-\sqrt{uz}>0.
\tag{SNC.22}
$$
对实轴有限 signed 测度 $\sigma$，明确要求三个指数核对其总变差可积。
定义真实可积非负核
$$
q_\tau(t)=e^{-mt}\bigl[\cosh(\delta(t-\tau))-1\bigr]
=\tfrac12e^{-\delta\tau}e^{-at}
 +\tfrac12e^{\delta\tau}e^{-bt}-e^{-mt}.
\tag{SNC.23}
$$
这三个实际核的线性式直接支付其可积性，不对未知测度求导。

**定理 459.5（全实谱率的必要加权抵消预算）。** 若上述三个节点的
最大误差不超过 $\varepsilon$，则
$$
\int q_\tau\,d\sigma^-
\ge d_G-(1+\cosh(\delta\tau))\varepsilon.
\tag{SNC.24}
$$
若进一步有 $\operatorname{supp}\sigma^-\subset[\tau-T,\tau+T]$，
$T>0$，则
$$
\boxed{\quad
\int e^{-mt}\,d\sigma^-
\ge\frac{[d_G-(1+\cosh(\delta\tau))\varepsilon]_+}
           {\cosh(\delta T)-1}.\quad}
\tag{SNC.25}
$$
对于精确拟合 $\varepsilon=0$，（SNC.25）是准确最小值，并且唯一达到测度为
$$
n=\frac{d_G}{\cosh(\delta T)-1},\qquad
\sigma=(v+n)e^{m\tau}\delta_\tau
-\frac n2e^{m(\tau-T)}\delta_{\tau-T}
-\frac n2e^{m(\tau+T)}\delta_{\tau+T}.
\tag{SNC.26}
$$
此 sharp 构造属于全实谱率类；若额外要求非负率，还须 $T\le\tau$。

**证明。** 目标数据代入（SNC.23）得
$\frac12e^{-\delta\tau}u+\frac12e^{\delta\tau}z-v
=\sqrt{uz}-v=-d_G$。真实误差盒给
$\int q_\tau d\sigma\le-d_G+(1+\cosh(\delta\tau))\varepsilon$。
又有 $\int q_\tau d\sigma=\int q_\tau d\sigma^+-\int q_\tau d\sigma^-$，
正部积分非负，即得（SNC.24）。在指定负谱支持上，
$q_\tau(t)\le e^{-mt}(\cosh(\delta T)-1)$，给（SNC.25）。

（SNC.26）三个原子不同，负部的中点加权质量为 $n$。
中点净值为 $v$，两端净值分别为
$e^{\delta\tau}[v-n(\cosh(\delta T)-1)]=u$
与 $e^{-\delta\tau}[v-n(\cosh(\delta T)-1)]=z$。
因此它精确拟合且达到下界。达到下界迫使正部支撑在 $t=\tau$，
负部支撑在 $t=\tau\pm T$；两个经倾斜的端点相等又迫使负部的
中点加权质量各为 $n/2$，故唯一性成立。证毕。

在 $a=h,b=2h$ 上，既有 $K_h/h^2\to c/72$ 与（SNC.1）给
$$
d_G/h^2=\frac{\Delta/h^2}{v+\sqrt{uz}}\longrightarrow c/36,
\qquad\tau\longrightarrow1/3.
$$
因此固定 $T>0$ 的精确最小中点加权负质量满足
$$
\frac{d_G}{\cosh(hT/2)-1}\longrightarrow\frac{2c}{9T^2}.
\tag{SNC.27}
$$
即使允许误差 $o(h^2)$，（SNC.25）也保留相同必要下极限。

**定理 459.6（全实率没有无支持约束的正负质量下界）。**
对于任意上述固定严格凹三点，存在有限两原子 signed 测度序列精确拟合
$u,v,z$，且其原始负质量和中点加权负质量均趋于零。

**证明。** 记 $\Delta=v^2-uz>0$。对充分大 $R>0$，置
$$
A_R=u e^{\delta R}+z e^{-\delta R}-2v>0,
\qquad n_R=\Delta/A_R,
$$
$$
U_R=u+n_Re^{-\delta R},\quad Z_R=z+n_Re^{\delta R},
\quad t_R=\frac{\log(U_R/Z_R)}{2\delta}.
$$
线性代数精确给 $U_RZ_R=(v+n_R)^2$。因此
$$
\sigma_R=(v+n_R)e^{mt_R}\delta_{t_R}
          -n_Re^{-mR}\delta_{-R}
\tag{SNC.28}
$$
在三个节点均精确拟合。这里
$t_R\to\log(u/v)/\delta>0$，故充分大时两个原子不同，负部确为后一项。
由 $n_R\sim(\Delta/u)e^{-\delta R}$，有
$$
\int e^{-mt}d\sigma_R^-=n_R\to0,
\qquad N_-(\sigma_R)=n_Re^{-mR}
\sim(\Delta/u)e^{-bR}\to0.
$$
每个测度都只有两个有限实位置，故所有所需核真正可积。
（SNC.24）的加权核预算仍成立，因为逃逸原子上的核足够大。
这说明非负率假设在原始负质量问题中承担实际内容。证毕。

### 459.5 保持原 Möbius 有限配对的精确运输与缺口

固定真实 $x\ge e$ 与整数 $N\ge\lceil8x\rceil$，保持同一实际阶乘核
$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad w(t)=\frac{1+\log t}{t^2\log^2t},
$$
$$
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)dt,
\quad J_x^\eta(n)=P_x^\eta(n)-P_x^\eta(n+1),
\quad\mathscr D_x(m)=P_x^\eta(m)-P_x^\eta(2m)
=\sum_{n=m}^{2m-1}J_x^\eta(n).
\tag{SNC.29}
$$
§455.6 的真实有限读数是
$$
O(n)=\sum_{\substack{m\le n\\m\text{ odd}}}\mu(m),\qquad O(0)=0,
\quad\mathcal L_x(n)=J_x^\eta(n)-J_x^\eta(2n)-J_x^\eta(2n+1),
\quad\mathscr F_x(N)=\sum_{n=1}^NO(n)\mathcal L_x(n),
$$
其中 $O(N)$ 始终是这个真实奇 Möbius 前缀，不是 Landau 大 $O$ 记号；
$$
\mathscr T_x(N)=\sum_{\substack{m\le N\\m\text{ odd}}}\mu(m)\mathscr D_x(m)
=\mathscr F_x(N)+O(N)\mathscr D_x(N+1)
=\mathscr C_{x,N}-\mathcal A_x,
$$
$$
I_\psi(x)=\mathscr T_x(N)+\mathscr R_x(N).
\tag{SNC.30}
$$
这些已有等式包含单位 $m=1$、全部奇来源、每份完整偶倍纤维及完整余项。
使用实际 $\eta$ 后，上游 $\beta_d$ 的完整运输已保留，未作新的 $\beta$ 截断。

现在按每个系数的真实符号定义有限谱
$$
a_{x,m}=\mu(m)\mathscr D_x(m),\qquad
\sigma_{x,N}=\sum_{\substack{m\le N\\m\text{ odd}}}a_{x,m}\delta_{\log m},
$$
$$
L_{x,N}(s)=\int e^{-st}d\sigma_{x,N}(t)
=\sum_{\substack{m\le N\\m\text{ odd}}}a_{x,m}m^{-s}.
\tag{SNC.31}
$$
所有谱率都非负，且 $L_{x,N}(0)=\mathscr T_x(N)$ 精确成立。
不同整数有不同谱位置，所以真实 Jordan 负质量为
$$
N_-(\sigma_{x,N})
=\sum_{\substack{m\le N\\m\text{ odd}}}(-a_{x,m})_+.
\tag{SNC.32}
$$
本式不把 $\mu(m)=-1$ 自动当成负部：必须同时保留真实
$\mathscr D_x(m)$ 的符号。§453 的真实素数面板在其已付共同阈值后
确有 $\mathscr D_x(p)>0$，它们对（SNC.32）贡献精确的 $\mathcal A_x$；
这复用既有面板供应，不是全配对符号结论。

这份实际有限谱还有真实截止 $0\le\log m\le\log N$。所以若未来支付
（SNC.36）的 $o(h^2)$ 误差，而所选联合尺度满足
$\log N\to\infty$、$h\log N\to0$，推论 459.4 会给
$$
\liminf (\log N)^2
\sum_{\substack{m\le N\\m\text{ odd}}}(-\mu(m)\mathscr D_x(m))_+
\ge2c/9.
\tag{SNC.33}
$$
例如 $h=x^{-1/4}(\log x)^{-1/2}$ 与 $N\asymp x^A$（固定 $A>1$）
满足这些截止条件；无截止的最优负原子则对应
$m=e^{t_-}\asymp\exp(2\log2/h)$，远超该多项式截止。
（SNC.33）仍明确条件于尚缺的逼近供应。既有真实素数面板本就支付了
$1/\log^2x$ 级负来源，这个条件约束不是新的无条件全配对障碍。

平方见证运输到同一实际有限配对后，得到无条件精确恒等式
$$
\begin{aligned}
Q_{x,N}(h,r)
&=L_{x,N}(2h)-2rL_{x,N}(3h/2)+r^2L_{x,N}(h)\\
&=\sum_{\substack{m\le N\\m\text{ odd}}}
a_{x,m}m^{-h}(m^{-h/2}-r)^2.
\end{aligned}
\tag{SNC.34}
$$
若 $r_*<r<1$，其正负源逐项给
$$
\sum_{a_{x,m}<0}|a_{x,m}|m^{-h}(m^{-h/2}-r)^2
\ge-Q_{x,N}(h,r),
$$
$$
-Q_{x,N}(h,r)\le (r^4/16)N_-(\sigma_{x,N}).
\tag{SNC.35}
$$
有限和直接支付交换、核可积性和每个符号；这是忠实的谱运输。

若未来在同一个 $x,N,h,c$ 上，对于 $0<h<h_0$ 与
$0\le\varepsilon\le K_h$ 真正支付
$$
\max_{s\in\{h,3h/2,2h\}}|cB(s)-L_{x,N}(s)|\le\varepsilon,
\tag{SNC.36}
$$
则定理 459.2 立即给同源负预算 $N_-(\sigma_{x,N})\ge n_\varepsilon$。
上述 §§448–450、453–457 的既有供应尚未支付（SNC.36）。
（SNC.30）只控制 $s=0$ 的真实读数；它既不是另外三个指数节点的身份，
也没有把那些节点自动送到 $cB$。
§449 的（HT.11）–（HT.17）支付的是实际 Fibonacci 对数导数尾
$I_F$ 到原 $I_\psi$ 的完整临界运输，也没有提供（SNC.36）的局部曲率谱逼近。

必须区分另一项已有真实谱：若
$z\ge2$、$L=\log z$、$P_z=\prod_{p\le z}p$、
$E_z(s)=\prod_{p\le z}(1-p^{-s})$、
$F_z(s)=E_z(1+s/L)/E_z(1)$，有限 Euler 展开确有
$$
F_z''(s)=\frac1{E_z(1)}\sum_{d\mid P_z}
\frac{\mu(d)}d\left(\frac{\log d}{L}\right)^2
e^{-s\log d/L}.
\tag{SNC.37}
$$
这个真实 finite primorial signed 曲率谱可以消费任何另行支付的
$F_z''$ 对 $B$ 的节点误差。它的系数是
$\mu(d)d^{-1}(\log d/L)^2/E_z(1)$、来源截止是 $d\mid P_z$，
不是（SNC.31）的 $\mu(m)\mathscr D_x(m)$ 与自然截止 $m\le N$。
特别是它的单位曲率系数为零，而（SNC.30）的原单位首块必须保留。
因此（SNC.37）不是（SNC.36）的运输证明。
同样，无权有限读出 $\sum_{m\le N,\ m\text{ odd}}\mu(m)m^{-s}$
在零点等于 $O(N)$，并不等于实际 $\mathscr T_x(N)$。

要把本节的逼近预算变成原 Robin 临界收益，还须支付（SNC.36）的
同源逼近或提供另一条明确的同源正负核恒等式，并控制（SNC.30）的完整
$\mathscr R_x(N)$。负谱不可缺少及其最小质量只说明必要抵消成本；
它没有给原 $I_\psi(x)$ 的临界符号下界，也没有改变完整 RH 目标。

### 459.6 来源、同对象新增结论与界限

平方见证、Jordan 分解、三点矩线性代数、指数核与有限和属于经典工具。
本节在实际 $B=\Phi''$ 上新增的精确结果是（SNC.8）–（SNC.19）：
允许误差盒下的最小原始负质量、唯一两原子最优谱、统一乘法系数 $64$
及精确拟合常数 $8c/9$。全实率上的中心加权支持预算与精确逃逸构造
补齐这一结果的适用边界。（SNC.34）–（SNC.37）给出真实算术来源的精确接口，
并明确保留尚缺的（SNC.36）；不对这些经典供应或全局文献原创性作额外断言。

## 追加锚（本行以下为增补区）

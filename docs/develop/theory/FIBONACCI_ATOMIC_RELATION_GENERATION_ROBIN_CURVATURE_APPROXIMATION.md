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

## 460. 原曲率负谱最优性的精确缺口与必须保留的算术单位原子

本节复用 §459 的同一实际 $B=\Phi''$、固定 $c>0$、三个节点
$h,3h/2,2h$、共同小窗口 $0<h<h_0$ 以及 $0\le\varepsilon\le K_h$。
沿用 $U,V,Z,r=r_\varepsilon,n=n_\varepsilon$，并记
$$
y(t)=e^{-ht/2},\qquad q(t)=y(t)^2(y(t)-r)^2,
\quad M=r^4/16,\quad \alpha=r^2/4+r-1>0.
\tag{SDD.1}
$$
这里 $r_*=2(\sqrt2-1)<r<1$、$M>0$ 和 $\alpha>0$ 均由 §459.1 的同一域支付。
测度始终是非负谱率上的真实有限 signed Borel 测度，正负部始终取 Jordan 分解。

### 460.1 达到最小值的三个缺口分别非负

**定理 460.1（精确对偶缺口恒等式）。** 若 $E_h(\sigma)\le\varepsilon$，定义
$$
d_{\rm box}=r^2\bigl(U-L_\sigma(h)\bigr)
 +2r\bigl(L_\sigma(3h/2)-V\bigr)
 +\bigl(Z-L_\sigma(2h)\bigr).
\tag{SDD.2}
$$
则下列三项均非负，且有精确身份
$$
\boxed{\quad
M\bigl(N_-(\sigma)-n\bigr)
=d_{\rm box}+\int q\,d\sigma^+
 +\int(M-q)\,d\sigma^-.
\quad}
\tag{SDD.3}
$$
每个积分都对整条非负轴进行，没有截尾。

**证明。** 三节点误差盒给 $L_\sigma(h)\le U$、
$L_\sigma(3h/2)\ge V$、$L_\sigma(2h)\le Z$；由于 $r>0$，
（SDD.2）的三个加数均非负。§459 的同一平方见证满足 $0\le q\le M$，
故其余两个积分也非负，且有界核对有限 Jordan 部真正可积。
令 $Q=\int q\,d\sigma$。有限线性组合与 §459 的原数据恒等式给
$$
Q=L_\sigma(2h)-2rL_\sigma(3h/2)+r^2L_\sigma(h)
 =-Mn-d_{\rm box}.
$$
而 Jordan 分解给
$$
Q=\int q\,d\sigma^+-MN_-(\sigma)
       +\int(M-q)\,d\sigma^-.
$$
整理得到（SDD.3）。证毕。

这将最优性的剩余成本精确分成节点误差盒缺口、正部偏离平方零点的成本，
以及负部偏离平方最大点的成本。三个成本都不能靠另一个成本的符号取消。
当 $N_-=n$ 时，它们同时为零，复得 §459 的唯一两原子；
下面同时给出接近最优时的定量控制。

### 460.2 接近最优时的谱位置控制及正质量逃逸边界

**推论 460.2（两种准确的集中预算）。** 若定理 460.1 的候选还满足
$N_-(\sigma)\le n+\rho$，其中 $\rho\ge0$，则
$$
\int y^2(y-r)^2\,d\sigma^+\le M\rho,
\qquad
\int(y-r/2)^2\,d\sigma^-\le\frac{M\rho}{\alpha},
\quad d_{\rm box}\le M\rho.
\tag{SDD.4}
$$
因而对每个 $a>0$ 有
$$
\sigma^-\{t:|y(t)-r/2|\ge a\}
\le\frac{M\rho}{\alpha a^2},
$$
$$
\int_{\{|y-r|\ge a\}}y^2\,d\sigma^+
\le\frac{M\rho}{a^2}.
\tag{SDD.5}
$$
若正部另有真实支持截止 $t\le T$，则还得到原始正质量控制
$$
\sigma^+\{t:|y(t)-r|\ge a\}
\le\frac{M\rho e^{hT}}{a^2}.
\tag{SDD.6}
$$
没有这一截止时，（SDD.5）只控制所写的加权正质量。

**证明。** （SDD.3）的三个非负项分别不超过 $M\rho$。
对于 $0\le y\le1$，准确因式分解为
$$
M-y^2(y-r)^2
=(y-r/2)^2\bigl(r^2/2-(y-r/2)^2\bigr).
\tag{SDD.7}
$$
因为 $0<r<1$，有 $|y-r/2|\le1-r/2$，所以括号内至少为
$r^2/2-(1-r/2)^2=\alpha>0$。积分给（SDD.4）第二项；
其余项直接来自（SDD.3）。在各自所写集合上用距离平方至少为 $a^2$，
得到（SDD.5）。若 $t\le T$，则 $y^2=e^{-ht}\ge e^{-hT}$，
得到（SDD.6）。证毕。

正部不能无条件改成原始质量集中：有限谱率上的平方零点只有 $y=r$，
但 $q(t)\to0$ 当 $t\to\infty$。接近最优允许正质量逃向无穷谱率；
负部的最大点缺口则有（SDD.7）的统一正系数。这是两种集中结论的准确差别。

### 460.3 实际 Möbius 有限谱的单位成本

保持 §459.5 的原实际有限谱
$$
a_{x,m}=\mu(m)\mathscr D_x(m),\qquad
\sigma_{x,N}=\sum_{\substack{m\le N\\m\text{ odd}}}a_{x,m}\delta_{\log m},
\quad N\ge1.
\tag{SDD.8}
$$
不同 $m$ 的谱位置不同，故正负部由这些系数的真实符号确定。
特别地，必须保留的单位 $m=1$ 位于 $t=0$，系数
$a_{x,1}=\mathscr D_x(1)$；不能用单位曲率系数为零的另一 primorial 谱替换它。
令 $a_+=\max(a,0)$。

**推论 460.3（单位原子的严格额外成本）。** 若同一实际谱确实满足
尚需另外支付的三节点供应 $E_h(\sigma_{x,N})\le\varepsilon$，则
$$
N_-(\sigma_{x,N})\ge n+
\frac{(a_{x,1})_+(1-r)^2
       +(-a_{x,1})_+\bigl(M-(1-r)^2\bigr)}{M}.
\tag{SDD.9}
$$
当 $a_{x,1}\ne0$ 时，右边严格大于 $n$，不要求提前猜测该单位系数的符号。

**证明。** $y(0)=1$，故 $q(0)=(1-r)^2$。实际 Jordan 正部中的单位
贡献为 $(a_{x,1})_+q(0)$，负部中的单位缺口贡献为
$(-a_{x,1})_+(M-q(0))$。其余来源与节点缺口均非负，
由（SDD.3）得到（SDD.9）。$r<1$ 给 $q(0)>0$；
$r>r_*$ 给 $r^2/4>1-r$，从而 $M>(1-r)^2$。
因此非零单位系数在任一符号下都支付严格正成本。证毕。

对任意实际 $x,N,h,r$，不用三节点逼近供应也有下面的全来源恒等式：
$$
\begin{aligned}
M N_-(\sigma_{x,N})+Q_{x,N}(h,r)
={}&\sum_{a_{x,m}>0}a_{x,m}\,m^{-h}(m^{-h/2}-r)^2\\
 &+\sum_{a_{x,m}<0}|a_{x,m}|\,
       \bigl(M-m^{-h}(m^{-h/2}-r)^2\bigr).
\end{aligned}
\tag{SDD.10}
$$
这里求和始终遍及 $m\le N$ 的真实奇来源；所有核与符号都由有限和支付。
在 $r_*<r<1$ 时右边非负，并含上述单位贡献。
只有另付同源三节点供应之后，才能用原 $B$ 的 $n$ 代替左边的实际 $-Q/M$。

### 460.4 单位正系数的成本处于同一二阶尺度

**推论 460.4（单位成本的统一二阶系数）。** 在同一固定 $c>0$ 下，
当 $h\downarrow0$，以下估计对整个 $\varepsilon\in[0,K_h]$ 一致成立：
$$
r_\varepsilon=1-h/6+O(h^2),\qquad
\frac{(1-r_\varepsilon)^2}{M_\varepsilon}
=\frac49h^2+O(h^3).
\tag{SDD.11}
$$
因此，若满足推论 460.3 的一族真实候选有单位系数
$a_{x(h),1}\to a>0$，则
$$
\liminf_{h\downarrow0}
\frac{N_-(\sigma_{x(h),N(h)})-n_{\varepsilon_h}}{h^2}
\ge\frac{4a}{9}.
\tag{SDD.12}
$$
若另有 $\varepsilon_h/h^2\to\kappa$，则 $0\le\kappa\le c/72$，并有
$$
\liminf_{h\downarrow0}\frac{N_-(\sigma_{x(h),N(h)})}{h^2}
\ge\frac{8c}{9}-64\kappa+\frac{4a}{9}.
\tag{SDD.13}
$$
若单位系数趋于一个 $a<0$，则同样的候选满足
$\liminf N_-\ge|a|$，故 $N_-/h^2\to+\infty$。

**证明。** 原 $B$ 的二阶 Taylor 估计与 $0\le\varepsilon\le K_h=O(h^2)$
给 $U=c/2-ch/6+O(h^2)$、$V=c/2-ch/4+O(h^2)$ 一致成立。
又由 §459 的 $\Delta_\varepsilon=O(h^2)$ 和恒等式
$D_\varepsilon-V=8\Delta_\varepsilon/(D_\varepsilon+V)$，
有 $D_\varepsilon-V=O(h^2)$ 一致成立；所有分母都一致远离零。
于是
$r_\varepsilon=V/U-(D_\varepsilon-V)/(2U)=1-h/6+O(h^2)$。
代入 $M=r^4/16$ 得（SDD.11）。对单位系数的正极限，
在（SDD.9）中取正部项并除以 $h^2$ 得（SDD.12）；
复用 §459.3 的 $n_{\varepsilon_h}/h^2\to8c/9-64\kappa$ 得（SDD.13）。
对负极限，负部单位乘子 $1-(1-r)^2/M\to1$，
（SDD.9）及 $n\ge0$ 给所述正下界与发散。证毕。

本推论的单位系数极限是假设，不能从原有限谱定义自动取得。
如果实际单位系数随 $x$ 衰减，须按（SDD.9）的真实系数结算，
不能套用固定正极限来声称无条件额外常数。

### 460.5 结论的用途、来源与未决边界

§459 的两原子允许位置连续变化；原算术来源必须保留 $\log1=0$ 的单位原子。
（SDD.9）给出这一差别造成的准确成本，（SDD.4）–（SDD.7）给出其接近最优时的
谱位置限制。它们可以检验候选同源运输能否同时满足节点精度、截止与强制来源。
三点平方对偶、Jordan 分解、非负缺口及距离平方控制是经典工具；本节组合使用
§459 的同一最优参数，并保留实际 Möbius 系数、完整偶倍纤维与原单位。
不对这些工具作全局文献原创性声明。

本节是完整纸面证明，没有新增 Lean 验收声称。§459 的（SNC.36）同源逼近仍缺，
原 $I_\psi$ 的临界有符号下界和完整 RH 目标仍开放。

## 追加锚（本行以下为增补区）

## 461. 保留固定正单位原子的原曲率三点精确负质量

本节保持原实际 $B=\Phi''$、固定 $c>0$ 和节点 $h,3h/2,2h$。
固定单位是测度的真实约束 $\sigma(\{0\})=a$，不是可调参数或可删除的来源。
首先研究 $0\le a\le a_{\max}<c/2$ 的一个固定紧区间；
任一固定 $0<a<c/2$ 都可置于这样的区间中。
所有候选都是 $[0,\infty)$ 上的有限实 signed Borel 测度，成本为其真实
Jordan 负部的原始质量 $N_-(\sigma)$。

### 461.1 原数据、残余数据和同一个共同小窗口

沿用 §459 的实际值
$$
u=cB(h),\quad v=cB(3h/2),\quad z=cB(2h),
\qquad S=2v+u+z,\quad \Delta=v^2-uz,\quad K_h=\Delta/S.
$$
令
$$
u_a=u-a,\quad v_a=v-a,\quad z_a=z-a,
\qquad S_a=S-4a,
$$
$$
\Delta_a=v_a^2-u_a z_a
 =\Delta+a(u+z-2v),\qquad K_{a,h}=\Delta_a/S_a.
\tag{MU.1}
$$

**引理 461.1（紧单位区间的共同域）。** 存在仅依赖 $c,B,a_{\max}$ 的
固定 $h_1>0$，使全部 $0<h<h_1$、全部 $a\in[0,a_{\max}]$ 同时满足
$$
u_a>v_a>z_a>0,\qquad v_a>(u_a+z_a)/2,
\qquad \Delta_a>0,\quad S_a>0,
\quad 0<K_{a,h}<v_a.
\tag{MU.2}
$$
对于任意 $0\le\varepsilon\le K_{a,h}$，定义
$$
U_a=u_a+\varepsilon,\quad V_a=v_a-\varepsilon,
\quad Z_a=z_a+\varepsilon,
$$
$$
\Delta_{a,\varepsilon}=V_a^2-U_aZ_a
 =\Delta_a-S_a\varepsilon\ge0,
\qquad D_a=\sqrt{9V_a^2-8U_aZ_a}
 =\sqrt{V_a^2+8\Delta_{a,\varepsilon}},
$$
$$
r_a=\frac{3V_a-D_a}{2U_a},\qquad
n_a=\frac{8(V_a-U_ar_a)}{r_a^3},\qquad
W_a=\frac{U_a}{r_a^2}+\frac{n_a}{4}.
\tag{MU.3}
$$
同一个 $h_1$ 还可取到使整个上述 $a,\varepsilon$ 域同时满足
$$
r_*:=2(\sqrt2-1)<r_a<1,\quad W_a>0,\quad n_a\ge0;
\qquad n_a=0\ \Longleftrightarrow\ \varepsilon=K_{a,h}.
\tag{MU.4}
$$

**证明。** 原实际 $B$ 已有 $B(0)=1/2$、$B'(0)=B''(0)=-1/6$，
并在一个共同零邻域正、严格递减、严格凹。
由于 $c/2-a_{\max}>0$，缩小邻域后可使整个邻域内 $cB>a_{\max}$。
减去一个常数不改变严格递减和严格凹，所以得到残余正性和中点严格凹性。
正端点及严格算术平均不等式给 $v_a^2>u_a z_a$。
此外
$$
v_a S_a-\Delta_a=(v_a+u_a)(v_a+z_a)>0,
$$
故 $K_{a,h}<v_a$。

对允许的容差有 $U_a,Z_a,V_a>0$。
$U_aZ_a>0$ 给 $D_a<3V_a$，而 $\Delta_{a,\varepsilon}\ge0$ 给
$D_a\ge V_a$，因此
$$
0<r_a\le V_a/U_a<1.
$$
由 $V_a-U_ar_a=(D_a-V_a)/2$ 得 $n_a\ge0$，
且它为零恰在 $\Delta_{a,\varepsilon}=0$，即容差右端点。
$W_a>0$ 直接由定义支付。

令 $p_a=c/2-a$，其在固定紧区间一致远离零。
原二阶 Taylor 估计给 $\Delta_a=O(h^2)$ 一致于 a，
而 $S_a\to4p_a$，所以 $K_{a,h}=O(h^2)$ 也一致成立。
因此整个容差带上 $U_a,V_a,Z_a\to p_a$，
$\Delta_{a,\varepsilon}=O(h^2)$ 一致成立。
正分母上的连续公式使 $r_a\to1$ 一致成立。
由于 $r_*<1$，再缩小同一个 $h_1$ 即得 MU.4。
该窗口在 a、容差和候选测度选择之前固定。证毕。

### 461.2 固定单位约束的精确解与唯一性

沿用原误差
$$
E_h(\sigma)=\max_{s\in\{h,3h/2,2h\}}
 |cB(s)-L_\sigma(s)|,
\qquad L_\sigma(s)=\int e^{-st}\,d\sigma(t).
$$

**定理 461.2（固定正单位的完整三点成本）。** 在引理 461.1 的同一域内，
对每个 $\varepsilon\ge0$ 有
$$
\inf_{\substack{\sigma\text{ finite signed on }[0,\infty)\\
                  \sigma(\{0\})=a,\ E_h(\sigma)\le\varepsilon}}
N_-(\sigma)
=\begin{cases}
n_a,&0\le\varepsilon\le K_{a,h},\\
0,&\varepsilon\ge K_{a,h}.
\end{cases}
\tag{MU.5}
$$
所有最小值都真正达到。在 $0\le\varepsilon\le K_{a,h}$ 时，
达到测度唯一，并精确为
$$
t_{+,a}=-\frac2h\log r_a>0,\qquad
t_{-,a}=t_{+,a}+\frac{2\log2}{h}>t_{+,a},
$$
$$
\boxed{\quad
\sigma_{a,\varepsilon}
=a\delta_0+W_a\delta_{t_{+,a}}-n_a\delta_{t_{-,a}}.
\quad}
\tag{MU.6}
$$
在 $\varepsilon=K_{a,h}$ 时负部为零。
在 $\varepsilon>K_{a,h}$ 时不宣称唯一性，且事实上有多个零成本达到测度。

**证明：单位与残余的真实 Jordan 分离。** 如果 $a\ge0$ 且
$\sigma(\{0\})=a$，真实 Jordan 部在单点处不能同时有正质量；
故 $\sigma^+(\{0\})=a$、$\sigma^-(\{0\})=0$。
写
$$
\lambda=\sigma-a\delta_0.
$$
则 $\lambda(\{0\})=0$，而其两个 Jordan 部在零点都无原子，
在 $(0,\infty)$ 上与原测度的对应部分相同。因此
$$
N_-(\lambda)=N_-(\sigma),\qquad
L_\lambda(s)=L_\sigma(s)-a.
\tag{MU.7}
$$
反之，任一零点无原子的有限 signed 残余测度加回 $a\delta_0$
都满足原固定单位约束并保持成本。
这是对每个候选的精确双射，不是删除原单位或调节它的系数。
原误差因此恰为残余数据 $u_a,v_a,z_a$ 对 $L_\lambda$ 的三点误差。

**证明：残余对偶下界。** 令 $y=e^{-ht/2}\in(0,1]$，取
$$
q_a(t)=y^2(y-r_a)^2,
\qquad M_a=r_a^4/16.
$$
导数 $2y(y-r_a)(2y-r_a)$ 与 MU.4 给
$0\le q_a\le M_a$，有限谱率的唯一零点为 $y=r_a$，
唯一最大点为 $y=r_a/2$。
二次方程和 n 的定义给
$$
U_ar_a^2-3V_ar_a+2Z_a=0,
\qquad Z_a-2r_aV_a+r_a^2U_a=-M_an_a.
\tag{MU.8}
$$
残余误差盒与三个非零系数 $1,-2r_a,r_a^2$ 给
$$
\int q_a\,d\lambda
=L_\lambda(2h)-2r_aL_\lambda(3h/2)+r_a^2L_\lambda(h)
\le-M_an_a.
$$
真实 Jordan 分解则给
$$
\int q_a\,d\lambda
\ge-M_aN_-(\lambda).
$$
合成得 $N_-(\sigma)=N_-(\lambda)\ge n_a$。
所有核在整个非负轴有界，因此这些积分和有限线性组合都真正可积。
下界甚至适用于不限制零点原子的更大残余类；下面的达到测度位于原受限类。

**证明：达到与唯一性。** 取 MU.6 的残余两原子。
它们位于严格正且不同的真实有限谱率，$W_a>0$、$n_a\ge0$，
故与单位原子共同构成真实 Jordan 分解，负质量恰为 $n_a$。
直接计算
$$
\begin{aligned}
r_a^2(W_a-n_a/4)&=U_a,\\
r_a^3(W_a-n_a/8)&=V_a,\\
r_a^4(W_a-n_a/16)&=Z_a.
\end{aligned}
\tag{MU.9}
$$
第一式由 W 的定义，第二式由 n 的定义，第三式由 MU.8 的二次方程。
加回单位后原三个读数为 $u+\varepsilon,v-\varepsilon,z+\varepsilon$，
所以原误差恰为 $\varepsilon$。
真实有限原子使全部所需积分可积；固定单位系数始终等于 a。

若任一候选成本达到 $n_a$，上下界链全部等号。
正部的 $\int q_a$ 和负部的 $\int(M_a-q_a)$ 同时为零，
故残余 Jordan 部分别只能在上述两个有限率上。
误差盒三个严格非零系数又使读数全部为 $U_a,V_a,Z_a$，
质量由 MU.9 唯一确定。右端点 $n_a=0$ 同样使负部为零，
正部仍由唯一有限零点和节点读数唯一确定。

对于 $\varepsilon\ge K_{a,h}$，取已构造的
$\sigma_{a,K_{a,h}}$ 即得成本零，达到所有更大的容差；
成本非负说明最小值恰为零。
若容差严格大于 $K_{a,h}$，可将该测度的残余正质量 W 增加任意充分小正量。
三个核在非负轴至多 1，故所有节点误差增加不超过该小量，
仍在较大的误差盒内。位置严格正，单位系数不变，成本仍零，
因此唯一性确实不能延伸到严格较大的容差。证毕。

### 461.3 容差阈值的精确增量

**推论 461.3（无需渐近的阈值关系）。** 同一个允许的小窗口内，
$$
\boxed{\quad
K_{a,h}-K_h=\frac{a(u-z)^2}{S(S-4a)}.
\quad}
\tag{MU.10}
$$
因此 $K_{a,h}=K_h$ 当 a=0，而 $K_{a,h}>K_h$ 当 a>0。

**证明。** 置 $J=u+z-2v$。直接整理得
$$
S J+4\Delta=(u+z+2v)(u+z-2v)+4(v^2-uz)=(u-z)^2.
$$
用 MU.1 通分，得到 MU.10。
分母正且 $u>z$，所以所述严格性成立。证毕。

这保证全部原容差带 $0\le\varepsilon\le K_h$ 都位于残余允许域中。
当 a>0 且 $\varepsilon=K_h$ 时，原无单位约束的最小负质量为零，
但残余容差尚未达到 $K_{a,h}$，所以固定单位的 $n_a$ 仍严格正。

### 461.4 比单位单项预算严格更强的有限 h 身份

在共同原容差带 $0\le\varepsilon\le K_h$，沿用 §459–460 的原
$r=r_\varepsilon$、$n=n_\varepsilon$ 和 $M=r^4/16$。
原单位单项下界为 $n+a(1-r)^2/M$。

**定理 461.4（精确剩余成本）。** 若 a>0，则 $r_a<r$，并有
$$
\begin{aligned}
M\left[n_a-n-\frac{a(1-r)^2}{M}\right]
={}&W_a r_a^2(r_a-r)^2\\
 &+n_a\left[M-\frac{r_a^2}{4}
                 \left(\frac{r_a}{2}-r\right)^2\right]>0.
\end{aligned}
\tag{MU.11}
$$
它对每个允许的有限 h 成立，包括 $\varepsilon=K_h$。
a=0 时两边为零。

**证明。** 在同一个 epsilon 下，残余盒数据为
$U_a=U-a,V_a=V-a,Z_a=Z-a$。
将原 r 代入残余二次多项式，利用原二次方程得到
$$
U_ar^2-3V_ar+2Z_a
=-a(r^2-3r+2)=-a(r-1)(r-2)<0.
$$
该多项式在零处为 $2Z_a>0$，开口向上，
MU.3 的 $r_a$ 是其较小正根，故 $r_a<r$。

把 MU.6 的真实最优测度代入 §460 的原精确对偶缺口。
它的三个原读数恰为原盒顶点 $U,V,Z$，所以原 $d_{\rm box}=0$。
单位贡献是 $a(1-r)^2$；残余正原子的原 y 值为 $r_a$，
负原子的原 y 值为 $r_a/2$。
其余两个完整成本恰为 MU.11 右边。
原平方见证在整个非负轴不超过 M，故第二项非负；
而 $W_a>0,r_a>0,r_a\ne r$ 使第一项严格正。
整个受约束最优测度都保留于身份中，未把残余成本删除。
当 a=0 时残余参数与原参数完全相同，身份两边为零。证毕。

### 461.5 全容差带和紧单位区间上的准确二阶系数

**定理 461.5（统一二阶成本）。** 以下估计都一致于
$a\in[0,a_{\max}]$；涉及 epsilon 的估计还一致于
$0\le\varepsilon\le K_{a,h}$：
$$
\frac{\Delta_a}{h^2}
\longrightarrow\frac{c(2c-3a)}{72},\qquad
\frac{K_{a,h}}{h^2}
\longrightarrow k(a):=\frac{c(2c-3a)}{144(c-2a)},
\tag{MU.12}
$$
$$
\frac{n_a}{h^2}
=\frac{4c(2c-3a)}{9(c-2a)}
 -64\frac{\varepsilon}{h^2}+o(1).
\tag{MU.13}
$$
特别地，对精确拟合有
$$
\frac{n_{a,0}}{h^2}\longrightarrow
\frac{4c(2c-3a)}{9(c-2a)}.
$$
同一域内还有
$$
r_a=1-\frac{c}{6(c-2a)}h+O(h^2),\qquad
t_{+,a}=\frac{c}{3(c-2a)}+O(h),
\quad W_a=c/2-a+O(h).
\tag{MU.14}
$$

**证明。** 原 Taylor 估计为
$$
cB(s)=c/2-cs/6-cs^2/12+o(s^2).
$$
三个固定倍数节点给
$$
\Delta/h^2\to c^2/36,\qquad
(u+z-2v)/h^2\to-c/24.
$$
乘以紧区间内有界 a，MU.1 给 MU.12 第一项一致成立。
由于 $S_a\to2(c-2a)$ 且分母一致远离零，第二项也一致成立。
此外有准确乘子身份
$$
n_a=\frac{32\Delta_{a,\varepsilon}}
           {r_a^3(D_a+V_a)}
 =\frac{32S_a}{r_a^3(D_a+V_a)}(K_{a,h}-\varepsilon).
\tag{MU.15}
$$
其证明是 $n_a=4(D_a-V_a)/r_a^3$，再用
$(D_a-V_a)(D_a+V_a)=8\Delta_{a,\varepsilon}$。
$r_a\to1,S_a\to4p_a,D_a+V_a\to2p_a$ 一致且分母正，
故 MU.15 的乘子一致趋于 64。
$K_{a,h}/h^2$ 和 $\varepsilon/h^2$ 一致有界，得到 MU.13。
该乘子身份在容差右端点也完全合法，不除以可能为零的 $K_{a,h}-\varepsilon$。

对于 MU.14，二阶有界 Taylor 余项和 epsilon 的共同 $O(h^2)$ 域给
$$
U_a=p_a-ch/6+O(h^2),\qquad
V_a=p_a-ch/4+O(h^2)
$$
一致成立。准确关系
$D_a-V_a=8\Delta_{a,\varepsilon}/(D_a+V_a)=O(h^2)$
及一致正分母给
$r_a=V_a/U_a-(D_a-V_a)/(2U_a)$ 的所列展开。
取对数后得到严格正位置的展开；MU.15 给 $n_a=O(h^2)$，
再代入 W 的定义得到其展开。证毕。

**推论 461.6（额外成本的准确主项）。** 一致于同一个紧 a 区间和整个
原容差带 $0\le\varepsilon\le K_h$，
$$
n_a-\left[n_\varepsilon+
          \frac{a(1-r_\varepsilon)^2}{M_\varepsilon}\right]
=\frac{8a^2}{9(c-2a)}h^2+O(h^3).
\tag{MU.16}
$$
因此对每个固定 a>0，该差具有严格正二阶系数；
有限 h 的严格性已由 MU.11 单独支付，不靠渐近余项猜测。

**证明。** 原共同展开 $r=1-h/6+O(h^2)$ 与 MU.14 给
$$
r_a-r=-\frac{a}{3(c-2a)}h+O(h^2).
$$
MU.11 的第一项除以 $M=1/16+O(h)$ 后给
$8a^2h^2/[9(c-2a)]+O(h^3)$。
第二项可用 §460 的准确因式分解：
$$
M-\frac{r_a^2}{4}\left(\frac{r_a}{2}-r\right)^2
=\frac{(r_a-r)^2}{4}
  \left(\frac{r^2}{2}-\frac{(r_a-r)^2}{4}\right)=O(h^2).
$$
因 $n_a=O(h^2)$，此项除以 M 后只有共同 $O(h^4)$。
所以得到 MU.16。亦可由 MU.13、原 $n_\varepsilon$ 的统一展开和
§460 的单位二阶系数直接核对主项：
$$
\frac{4c(2c-3a)}{9(c-2a)}
 -\frac{8c}{9}-\frac{4a}{9}
=\frac{8a^2}{9(c-2a)}.
$$
前一精确身份证明同时支付了所写共同余项。证毕。

### 461.6 实际算术 head 的条件接口和未决范围

保持 §459–460 的同一真实有限奇 Möbius 谱
$$
\sigma_{x,N}=\sum_{\substack{m\le N\\m\text{ odd}}}
 \mu(m)\mathscr D_x(m)\delta_{\log m},\qquad N\ge1.
$$
不同自然来源有不同谱位置，所以该谱的固定单位系数确实是
$a_{x,1}=\mathscr D_x(1)$，其余奇来源均有严格正谱率。
**只有另行支付**
$$
0\le a_{x,1}\le a_{\max}<c/2,\qquad
0<h<h_1,\qquad E_h(\sigma_{x,N})\le\varepsilon
\tag{MU.17}
$$
时，才能把本节用于该同一个谱，得到其真实 Jordan 负质量至少为
MU.5 中的准确最小值。
若 $a_{x,1}>0$ 且 $\varepsilon\le K_h$，MU.11 给比 §460 单位单项更强的
精确下界，包括原 $n_\varepsilon=0$ 的右端点。
单位的真实数值在此被代入，不被删去、调节或用另一个 primorial 曲率谱替换。

若在该紧区间内 $a_{x(h),1}\to a_0$，且
$0\le\varepsilon_h\le K_{a_{x(h),1},h}$、
$\varepsilon_h/h^2\to\kappa$，那么
$0\le\kappa\le k(a_0)$，由一致估计可得条件下界
$$
\liminf\frac{N_-(\sigma_{x(h),N(h)})}{h^2}
\ge\frac{4c(2c-3a_0)}{9(c-2a_0)}-64\kappa.
\tag{MU.18}
$$
这一单位系数极限和同源节点逼近都是另外的实际供应，不从有限谱定义自动取得。

上述连续率最优测度只说明固定单位比较类的下界准确，
不说明原 Möbius 系数和整数对数位置能够达到它。
真实原谱的完整偶倍纤维、有限截止、全部来源及完整余项仍须保留；
尤其 §459 的 SNC.36 节点运输和原 $I_\psi$ 临界有符号尾仍未支付。
已有 Fibonacci 完整尾运输不自动提供这三个曲率节点。

边界 a=0 被 MU.5–MU.16 完整覆盖，成本与 §459 相同，
达到测度本来就没有零点原子。
$a\uparrow c/2$ 不能用本紧区间的一致正分母外推；
a>=c/2、固定负单位、真实 $a_{x,1}$ 的正性和尺度供应不在本节解决范围内。
本节给出固定单位比较类的精确下界；原临界有符号尾仍然开放。


### 461.7 来源与数学连接

本节复用 §459 的三核平方对偶和两原子代数，以及 §460 的完整非负缺口。
Jordan 分解、有限谱、Taylor 估计和一致正分母是经典工具。
原 $\Phi$、零值和导数来源保持 PrimorialGlobalLaplaceEnvelope、
PrimePrefixPhiCurvature 及其原供应 PrimorialFirstOrderConcentrationCounterexample；
实际 Möbius 配对保持 §§455.6、459.5 的全部来源。
这些经典供应和既有结果不作新的原创性声明。

固定算术单位将三点矩问题变成一个平移后的精确约束问题。
零点的 Jordan 分离保留了原始负质量，新的残余正原子率由剩余质量决定，
其位置偏移在原平方对偶中支付严格的额外成本。
因此原单位的系数、剩余质量与三个节点的共同容差必须一起控制；
三者的同源供应是将此比较结果用于实际有限 head 的条件。

## 追加锚（本行以下为增补区）

## 462. 原实际曲率的完整指数底座与原 A 的严格正储备

保持同一原函数与完整常数

$$
\Phi(v)=\exp\!\left(\int_0^1\frac{1-e^{-vt}}t\,dt\right),
\quad B(v)=\Phi''(v),\quad
\gamma=\gamma_E,\quad C=e^\gamma,\quad k=C-1,
$$

$$
A=\int_0^1\frac{\Phi'(v)-1}{v}\,dv
 +\int_1^\infty\frac{\Phi'(v)-C}{v}\,dv.
\tag{EFA.1}
$$

本节从原曲率的完整指数底座推导同一原 A 的严格正下界。

### 462.1 原对象与完整积分供应

复用 §450 的完整端点、质量、矩和对数积分供应：

$$
B(0)=\tfrac12,\quad B(v)>0\ (v>0),\quad
\int_0^\infty B(v)\,dv=k,\quad
\int_0^\infty vB(v)\,dv=1,
$$

$$
\int_0^\infty |\log v|B(v)\,dv<\infty,\qquad
A=-\int_0^\infty\log v\,B(v)\,dv.
\tag{EFA.2}
$$

其零点连续性和导数绑定保持 PrimePrefixPhiCurvature；
原归一化和完整两段 A 保持 PrimePrefixOriginalA；
上述全部矩保持 PrimePrefixCurvatureMoments。
也复用 §450 的同一正轴 Euler 表示

$$
E_1(v)=\int_v^\infty\frac{e^{-w}}w\,dw,\quad
0<E_1(v)\le e^{-v}/v,\quad
\Phi(v)=Cv e^{E_1(v)},\quad
\Phi'(v)=\Phi(v)\frac{1-e^{-v}}v,
$$

$$
B(v)=\Phi(v)e^{-v}\frac{v-1+e^{-v}}{v^2}
=C e^{E_1(v)}e^{-v}
 \left(1-\frac{1-e^{-v}}v\right)\qquad(v>0).
\tag{EFA.3}
$$

这些是原函数已经证明的性质，不是对未知 B 的替代假设。

经典完整积分

$$
\int_0^\infty e^{-v}\,dv=1,\quad
\int_0^\infty ve^{-v}\,dv=1,\quad
\int_0^\infty \log v\,e^{-v}\,dv=-\gamma
\tag{EFA.4}
$$

沿用 Gamma 的已有供应。末项绝对收敛：近端由 $\int_0^1|\log v|dv=1$ 支付，远端由 $\log v\le v$ 和指数衰减支付。
原 OriginalA 的归一化复用 Mertens.Gamma 中的完整积分恒等式
$\int\log v\,e^{-v}=\Gamma'(1)$，该供应保持 PrimeNumberTheoremAnd 端口来源。
Gamma 积分的导数定理及 $\gamma=-\Gamma'(1)$ 复用 Mathlib 的
Complex.hasDerivAt_GammaIntegral 和 Real.eulerMascheroniConstant_eq_neg_deriv。

### 462.2 完整正轴上的严格指数底座

**定理 462.1（原曲率的指数底座）。** 连续延拓到零点的

$$
F(v)=e^vB(v)\quad(v\ge0)
$$

在整个非负轴严格递增，且

$$
F(0)=\tfrac12,\qquad \lim_{v\to\infty}F(v)=C.
\tag{EFA.5}
$$

因此对全部 $v>0$，

$$
\boxed{\qquad \tfrac12e^{-v}<B(v)<Ce^{-v}.\qquad}
\tag{EFA.6}
$$


**证明。** 对 $v>0$，置 $g(v)=(v-1+e^{-v})/v^2$。
EFA.3 给 $F=\Phi g$，直接求导并使用原 $\Phi'/\Phi=(1-e^{-v})/v$，得

$$
\begin{aligned}
F'(v)
&=\frac{\Phi(v)}{v^3}
 \left[(1-e^{-v})(v-1+e^{-v})
       +v(1-e^{-v})-2(v-1+e^{-v})\right]\\
&=\frac{\Phi(v)}{v^3}
 \left(1-2ve^{-v}-e^{-2v}\right)\\
&=\frac{\Phi(v)e^{-v}}{v^3}
 \left(e^v-e^{-v}-2v\right)>0.
\end{aligned}
\tag{EFA.7}
$$

最后的严格正性可完全用原实指数函数支付：令
$p(v)=e^v-e^{-v}-2v$，则 $p(0)=0$，而对 $v>0$，

$$
p'(v)=e^v+e^{-v}-2
=\left(e^{v/2}-e^{-v/2}\right)^2>0.
$$

因此 $p(v)>0$。没有对未知测度求导，也没有使用 A 的符号。

零点由 B 的实际连续性给 $F(0)=1/2$，不在 EFA.7 中代入 v=0。
对任意 $0\le a<b$，F 在 [a,b] 连续、在其开区间可微且导数严格正，均值定理给严格递增，包括 a=0 的情况。

无穷端由 EFA.3 准确写成

$$
F(v)=Ce^{E_1(v)}
 \left(1-\frac{1-e^{-v}}v\right).
$$

$E_1(v)\le e^{-v}/v\to0$，括号趋于 1，故 F 趋于 C。
严格递增和有限极限给 $1/2<F(v)<C$ 对每个 v>0 成立。
乘以 $e^{-v}>0$ 得 EFA.6。证毕。

### 462.3 抽出指数底座后的完整剩余律

定义实际剩余密度和质量

$$
R(v)=B(v)-\tfrac12e^{-v},\qquad
r=k-\tfrac12.
\tag{EFA.8}
$$

EFA.6 给 R(v)>0 于全部 v>0，且 R(0)=0。
经典 $\gamma>1/2$ 和 $e^\gamma\ge1+\gamma$ 给
$k\ge\gamma>1/2$，所以 r>0。

**引理 462.2（完整剩余质量与矩）。** 完整剩余积分满足

$$
\int_0^\infty R(v)\,dv=r,\qquad
\int_0^\infty vR(v)\,dv=\tfrac12,\qquad
\int_0^\infty|\log v|R(v)\,dv<\infty,
$$

$$
A=\frac\gamma2-\int_0^\infty\log v\,R(v)\,dv.
\tag{EFA.9}
$$

因此 $R(v)dv/r$ 是严格正的正轴概率密度，其均值为 $m=1/(2r)$；它没有零点原子，亦非点质量。

**证明。** R 连续，且 $0<R<B$ 对 v>0 成立。
EFA.2 已付 B、vB 和 $|\log v|B$ 的完整可积性，因此三种剩余核都绝对可积。用 EFA.2、EFA.4 和完整积分的线性性相减，分别得到质量 r、一阶矩 1/2 与所列原 A 身份。这里没有截取有限尾，也没有把两个不收敛的积分相减。正密度在每个正长度的正轴紧区间有正质量，故均值 m 是有限正数，律非退化。证毕。

### 462.4 剩余严格 Jensen 与原 A 的正性

**定理 462.3（原 A 的严格正储备）。** 原完整两段常数有精确更强的下界

$$
\boxed{\quad
A>\frac\gamma2+
 \left(k-\frac12\right)\log(2k-1).
\quad}
\tag{EFA.10}
$$

进而

$$
\boxed{\qquad \frac1{16}<A<\frac12.\qquad}
\tag{EFA.11}
$$


**证明：完整严格 Jensen。** 对 m=1/(2r)>0 和每个 v>0，实对数切线给

$$
\log v\le\log m+\frac{v-m}{m},
$$

等号仅在 v=m。线性项和对数项对 R(v)dv 全部绝对可积。
切线差非负，并在例如 [m+1,m+2] 上严格正，R 在该紧区间严格正；
连续非负函数的该段积分严格正。因而

$$
\int_0^\infty\log v\,R(v)\,dv
<r\log m+\frac1m\left(\tfrac12-mr\right)
=r\log m.
$$

代入 EFA.9，并用 $-\log m=\log(2r)$，得 EFA.10。

**证明：统一严格数值储备。** 对任意 x>0，

$$
x\log x\ge-\frac1e.
\tag{EFA.12}
$$

例如把 $\log y\ge1-1/y$ 用于 y=ex，减去 1 后乘以 x，直接得此界；没有需要估计的局部最小值。
置 x=2r，EFA.10 给

$$
A>\frac\gamma2+r\log(2r)
\ge\frac\gamma2-\frac1{2e}.
$$

经典 $\gamma>1/2$ 已被原供应复用；
指数正项级数在 x=1 给

$$
e>1+1+\frac12+\frac16=\frac83.
$$

因此

$$
\frac\gamma2-\frac1{2e}>
\frac14-\frac3{16}=\frac1{16}.
$$

最后的上界 A<1/2 直接复用原 PrimePrefixOriginalA。
这整条链不使用待证的 A 正性或任何数值拟合。证毕。

### 462.5 原对数矩、信息散度与 Robin 供应边界

§450 和 PrimePrefixOriginalALogLowerBound 已有
$A=-\int\log v\,B(v)dv$ 及 $A>k\log k$。
这里的新增步骤是 EFA.5–EFA.7 的原曲率完整指数底座，以及把该底座完整抽出后使用真实正剩余律，得到 EFA.10–EFA.11。指数底座及剩余质量、一阶矩共同承担这一加强。

若另外沿用 $\mu(dv)=B(v)dv/k$、$\nu(dv)=vB(v)dv$，两者都是完整正轴概率律且相互绝对连续，
$d\nu/d\mu=kv$。EFA.2 支付对数似然比的绝对可积性，因此经典概率 KL 身份确为

$$
A-k\log k=kD_{\rm KL}(\mu\Vert\nu).
\tag{EFA.13}
$$

其严格非退化性复述已有原 Jensen gap；本节 EFA.10 的额外强度来自已经证明的实际指数底座，不依赖信息散度术语。

本结果仍是原实际常数的解析供应。它没有给真实 Möbius 谱的同源三节点逼近、原 Robin 配对的完整有符号尾或 RH 判据的最终符号；实际 Fibonacci 完整尾运输也不被当成这些未付供应。

### 462.6 来源与证明范围

原对象、完整端点、积分质量和对数矩复用 §§444、450 及
PrimorialGlobalLaplaceEnvelope、PrimePrefixPhiCurvature、PrimePrefixOriginalA、
PrimePrefixCurvatureMoments 的对应结果；完整 Gamma 对数矩保持
Mertens.Gamma 及其 PrimeNumberTheoremAnd 端口来源。指数函数、均值定理、完整积分线性性、
严格对数切线及 Gamma 对数矩属于经典工具。
本节的新增解析结论是 EFA.5–EFA.11；EFA.13 将既有严格对数切线缺口写为
原曲率律与其按变量加权的概率律之间的相对熵。
上述局部解析结论来自本仓原对象的推导，不作全球文献首创声明。
新增结论在此给出完整纸面证明，其 Lean 形式化另行交付。

## 追加锚（本行以下为增补区）

## 463. 原曲率的正 Volterra 递归与收敛到原 A 的严格下界

保持同一个原函数、原实际曲率和完整两段常数：

$$
\Phi(v)=\exp\!\left(\int_0^1\frac{1-e^{-vt}}t\,dt\right),
\qquad B(v)=\Phi''(v),\qquad
\gamma=\gamma_E,\quad C=e^\gamma,\quad k=C-1,
$$

$$
A=\int_0^1\frac{\Phi'(v)-1}{v}\,dv
 +\int_1^\infty\frac{\Phi'(v)-C}{v}\,dv.
\tag{RVF.1}
$$

本节构造原 B 的正积分递归。每个有限递归层都给出一个严格下界，
这些下界严格递增到同一个原 A；整个无穷尾有显式误差界。
下文未注明区间的积分一律是完整正轴上的 Lebesgue 积分
$\int_0^\infty$。零点没有原子，对数只在正轴上使用。

### 463.1 原对象与完整供应

复用 §§444、450、462 已支付的同一原对象性质：

$$
\Phi(0)=\Phi'(0)=1,\quad B(0)=\tfrac12,\quad
0<B(v)<\tfrac12\quad(v>0),
$$

$$
\int B=k,\qquad \int vB=1,\qquad
\int |\log v|B<\infty,\qquad A=-\int\log v\,B(v)\,dv,
\tag{RVF.2}
$$

$$
\tfrac12e^{-v}<B(v)<Ce^{-v}\quad(v>0).
\tag{RVF.3}
$$

原 $\Phi$ 及 B 的连续性、导数绑定来自 PrimePrefixPhiCurvature；
原归一化和完整两段 A 来自 PrimePrefixOriginalA；
完整质量、一阶矩和绝对对数可积性来自 PrimePrefixCurvatureMoments。
RVF.3 是 §462 的实际指数底座，非另选一个满足矩约束的密度。
还复用 §462 已给出的同一原 F 的正轴导数身份：

$$
F(v)=e^vB(v),\qquad F(0)=\tfrac12,\qquad
F'(v)=\Phi(v)e^{-v}\frac{e^v-e^{-v}-2v}{v^3}\quad(v>0).
\tag{RVF.4}
$$

以下先在有限区间建立精确递归，再用 RVF.2–RVF.3 处理完整积分。

### 463.2 递归系数的零端点与完整正指数表示

置

$$
p(v)=e^v-e^{-v}-2v,\qquad
a(v)=\begin{cases}e^{-v}p(v)/v^3,&v>0,\\[2pt]1/3,&v=0.\end{cases}
\tag{RVF.5}
$$

**引理 463.1（系数的完整表示）。** 对全部 $v\ge0$，

$$
\boxed{\quad
a(v)=\frac12\int_0^1(1-t)^2
 \left[e^{-v(1-t)}+e^{-v(1+t)}\right]dt.
\quad}
\tag{RVF.6}
$$

因此 a 在非负轴连续，且

$$
a(0)=\tfrac13,\qquad 0<a(v)\le\tfrac13\quad(v\ge0),
\qquad a(v)<\tfrac13\quad(v>0).
\tag{RVF.7}
$$

**证明。** $p(0)=p'(0)=p''(0)=0$ 且 $p'''(s)=e^s+e^{-s}$。
有限区间上的三次 FTC 或 Taylor 积分余项给

$$
p(v)=\frac12\int_0^v(v-s)^2(e^s+e^{-s})\,ds\qquad(v\ge0).
\tag{RVF.8}
$$

对 v>0 乘以 $e^{-v}/v^3$ 并置 s=vt，得到 RVF.6。
右侧在 v=0 的值是 $\int_0^1(1-t)^2dt=1/3$，且其被积函数在每个
有限参数窗口联合连续，故它给出准确的连续零端点。
两指数均严格正，且在 v,t 的所列域均不超过 1，得到 RVF.7 的
正性和上界。v>0 时第二指数在整个 [0,1] 小于 1，权重在 [0,1) 正，
故积分上界严格。证毕。

换元还把同一系数写成紧支撑的正 Laplace 混合：

$$
a(v)=\int_0^2 e^{-\lambda v}w(\lambda)\,d\lambda,
\qquad
w(\lambda)=\begin{cases}
\lambda^2/2,&0\le\lambda\le1,\\
(2-\lambda)^2/2,&1\le\lambda\le2.
\end{cases}
\tag{RVF.9}
$$

两段在 λ=1 一致，且 $\int_0^2w=1/3$。
右侧还定义全实轴上的光滑延拓，以下导数使用该延拓。
有限 λ 区间允许逐次在积分号下求导；因而对每个整数 j≥0 和 v≥0，
$(-1)^ja^{(j)}(v)=\int_0^2\lambda^je^{-\lambda v}w(\lambda)d\lambda>0$。
这里的正指数混合属于递归系数 a。

### 463.3 同一原 B 的精确正 Volterra 方程

**定理 463.2（原对象的递归方程）。** 对任意连续
$f:[0,\infty)\to\mathbb R$，定义仅涉及有限连续积分的

$$
b(v)=e^{-v}\left[\frac12+\int_0^v a(s)(1+s)\,ds\right],
$$

$$
(Tf)(v)=e^{-v}\int_0^v a(s)
 \int_0^s(s-t)f(t)\,dt\,ds.
\tag{RVF.10}
$$

则 b 和 Tf 连续，$b(v)>0$ 对全部 v≥0 成立，并且

$$
\boxed{\qquad B=b+TB.\qquad}
\tag{RVF.11}
$$

**证明。** 原 $\Phi(0)=\Phi'(0)=1$ 和 $\Phi''=B$ 的两次有限 FTC 给

$$
\Phi(s)=1+s+\int_0^s(s-t)B(t)\,dt\qquad(s\ge0).
\tag{RVF.12}
$$

RVF.4 在正轴上是 $F'=a\Phi$。对 $0<\varepsilon<v$ 用 FTC，再令
ε↓0。F 的实际连续性和 aΦ 在 [0,v] 的连续性分别支付两端极限，得到

$$
B(v)=e^{-v}\left[\frac12+\int_0^v a(s)\Phi(s)\,ds\right].
\tag{RVF.13}
$$

v=0 时此式同样由 B(0)=1/2 成立；不向 RVF.4 的除式代入零点。
把 RVF.12 代入 RVF.13，准确得到 RVF.10–RVF.11。
连续性来自有限参数积分，b 的正性来自括号内的正常数和非负积分。
证毕。

有限三角域上的 Fubini 给同一个算子的核表示

$$
(Tf)(v)=\int_0^vK(v,t)f(t)\,dt,\qquad
K(v,t)=e^{-v}\int_t^v a(s)(s-t)\,ds.
\tag{RVF.14}
$$

K 在 $0\le t\le v$ 的每个紧三角域连续，K(v,v)=0，且
K(v,t)>0 对 $0\le t<v$ 成立。特别地，T 是线性正算子；若
f 在整个正轴严格正，则 Tf(v)>0 对每个 v>0 成立。
最后的严格性可在 $t\in[v/4,v/2]$ 上积分连续严格正函数支付。
这里只交换有限积分，未要求一般 f 在无穷轴可积。

### 463.4 每一个有限递归层与端点严格性

定义自然数指标的递归、真实剩余与新增层

$$
B_0=0,\qquad B_{n+1}=b+TB_n,\qquad
R_n=B-B_n,\qquad D_n=B_{n+1}-B_n.
\tag{RVF.15}
$$

**定理 463.3（严格正的实际分层）。** 对每个 n≥0，

$$
R_n=T^nB,\qquad D_n=T^nb,\qquad
R_n=R_{n+1}+D_n,
\tag{RVF.16}
$$

$$
0\le B_n(v)<B_{n+1}(v)<B(v)\quad(v>0),\qquad
R_n(v)>0,\quad D_n(v)>0\quad(v>0).
\tag{RVF.17}
$$

全部函数连续。零端点准确为

$$
\begin{gathered}
B_0(0)=0,\quad B_n(0)=\tfrac12\ (n\ge1),\\
R_0(0)=\tfrac12,\quad R_n(0)=0\ (n\ge1),\\
D_0(0)=\tfrac12,\quad D_n(0)=0\ (n\ge1).
\end{gathered}
\tag{RVF.18}
$$

**证明。** RVF.11 和线性性给
$R_{n+1}=T(B-B_n)=TR_n$；R0=B，故 $R_n=T^nB$。
同理 D0=b、$D_{n+1}=TD_n$，得到第二个身份。第三个身份由定义相减。
原 B 和 b 在正轴严格正，RVF.14 的严格正算子性质归纳给所有
R_n、D_n 的正性。B0=0，$B_{n+1}=B_n+D_n$，故 Bn 非负且严格递增；
Rn>0 给对 B 的严格上界。连续性逐层由 RVF.10 得到。
最后 $(Tf)(0)=0$、b(0)=1/2 给 RVF.18 的每一项。
所有有限层的严格不等式均明确位于 v>0。证毕。

### 463.5 三重积分的阶乘误差与实际曲率的局部一致恢复

**定理 463.4（全轴逐点界与紧窗一致收敛）。** 置

$$
c_n=\frac1{2\cdot3^n(3n)!}.
$$

则对全部 n≥0 和 v≥0，

$$
\boxed{\qquad 0\le R_n(v)\le c_nv^{3n}.\qquad}
\tag{RVF.19}
$$

每个固定 V≥0 上，

$$
\sup_{0\le v\le V}|B(v)-B_n(v)|\le c_nV^{3n}\longrightarrow0.
\tag{RVF.20}
$$

特别地，同一个原曲率有正层展开

$$
B_n=\sum_{j=0}^{n-1}T^jb,\qquad
B=\sum_{j=0}^\infty T^jb,
\tag{RVF.21}
$$

n=0 时有限和为空。无穷和在每个紧窗一致收敛，在完整非负轴逐点成立。

**证明。** RVF.7 和 $e^{-v}\le1$ 给

$$
0\le K(v,t)\le\frac{(v-t)^2}{6}\qquad(0\le t\le v).
\tag{RVF.22}
$$

RVF.19 的 n=0 是原 $B\le1/2$。若 n 的界成立，则由 Rn+1=TRn，

$$
R_{n+1}(v)\le\frac{c_n}6\int_0^v(v-t)^2t^{3n}\,dt
=\frac{c_n}3\frac{(3n)!}{(3n+3)!}v^{3n+3}
=c_{n+1}v^{3n+3}.
\tag{RVF.23}
$$

中间积分用整数幂展开积分或 Beta 积分均可直接得到；这是有限积分。
对 V>0，RVF.20 右侧相邻项比值是
$V^3/[3(3n+1)(3n+2)(3n+3)]\to0$，故趋零；V=0 由 RVF.18 单独给出。
有限和身份由递归归纳，无穷和身份由 RVF.20 取极限。
证毕。

每轮恰好累加三次有限积分的阶数，因而出现 (3n)!。
局部一致收敛由这一 Volterra 三角域结构保证。
完整无穷轴的积分收敛在下一小节由原完整供应支付。

### 463.6 全部剩余质量、矩与对数积分

定义完整剩余预算和新增层预算

$$
r_n=\int R_n,\quad m_n=\int vR_n,\qquad
z_n=\int D_n,\quad t_n=\int vD_n.
\tag{RVF.24}
$$

**引理 463.5（完整可积性与极限）。** 对每个有限 n，Bn、Rn、Dn
以及各自乘以 v、$|\log v|$ 的函数，在完整正轴上可积。并且

$$
r_n=k-\int B_n>0,\qquad m_n=1-\int vB_n>0,
\qquad z_n>0,\quad t_n>0,
$$

$$
r_n=r_{n+1}+z_n,\qquad m_n=m_{n+1}+t_n,
\tag{RVF.25}
$$

$$
r_n\downarrow0,\qquad m_n\downarrow0,\qquad
\ell_n:=\int|\log v|R_n(v)\,dv\longrightarrow0.
\tag{RVF.26}
$$

因此

$$
\int B_n\longrightarrow k,\quad
\int vB_n\longrightarrow1,\quad
-\int\log v\,B_n(v)\,dv\longrightarrow A.
\tag{RVF.27}
$$

**证明。** RVF.16–RVF.17 给
$0\le B_n\le B$、$0\le R_n\le B$、$0\le D_n\le R_n\le B$。
RVF.2 的三种可积主导同时支付全部所列完整积分；有符号对数项
由相应绝对对数项支付。正密度在例如 [1,2] 上连续严格正，故其
质量和一阶矩均严格正。RVF.25 由完整可积积分的线性性得到。
RVF.20 给 Rn 逐点趋零。对 Rn、vRn 和 $|\log v|R_n$ 分别使用
B、vB、$|\log v|B$ 的 DCT，得到 RVF.26。
其中 rn、mn 的递减由 RVF.25 的严格正新增预算得到。
最后准确相减得到 RVF.27；有符号对数极限亦可直接由同一绝对主导得到。
整个论证保留无穷尾，并未从紧窗一致收敛直接推出无穷积分极限。证毕。

### 463.7 完整严格 Jensen 与预算合并

对正质量和正一阶矩定义

$$
\mathcal F(r,m)=r\log(r/m)\qquad(r,m>0).
\tag{RVF.28}
$$

**引理 463.6（严格密度 Jensen）。** 若连续密度 f 在正轴处处严格正，
f、vf、$|\log v|f$ 完整可积，r=∫f>0、m=∫vf>0，则

$$
\mathcal J(f):=-\int\log v\,f(v)\,dv>\mathcal F(r,m).
\tag{RVF.29}
$$

**证明。** 置 μ=m/r>0。对每个 v>0，实对数切线给

$$
\log v\le\log\mu+\frac{v-\mu}{\mu},
$$

等号仅在 v=μ。切线差乘以 f 后绝对可积；在 [μ+1,μ+2] 上连续
严格正，故完整积分严格正。于是
$\int\log v\,f<r\log\mu+(m-\mu r)/\mu=r\log\mu$。
取负号并用 $-\log\mu=\log(r/m)$ 得 RVF.29。证毕。

**引理 463.7（两个完整预算的合并）。** 对 r1,r2,m1,m2>0，

$$
\mathcal F(r_1,m_1)+\mathcal F(r_2,m_2)
\ge\mathcal F(r_1+r_2,m_1+m_2).
\tag{RVF.30}
$$

等号恰在 m1/r1=m2/r2 成立。

**证明。** 对权重 $r_i/(r_1+r_2)$ 使用实 log 的严格凹性：

$$
\frac{r_1}{r_1+r_2}\log\frac{m_1}{r_1}
+\frac{r_2}{r_1+r_2}\log\frac{m_2}{r_2}
\le\log\frac{m_1+m_2}{r_1+r_2}.
$$

乘以负数 $-(r_1+r_2)$ 得 RVF.30。
两权重严格正，故严格凹性的等号条件正是所列均值条件。证毕。

还需要一个不依赖 r 与 m 比值的完整界：

$$
\mathcal F(r,m)\ge-\frac m e\qquad(r,m>0).
\tag{RVF.31}
$$

事实上 q=r/m>0 给 $\mathcal F=mq\log q$，而经典
$q\log q\ge-1/e$ 可由 log 切线支付：将
$\log y\ge1-1/y$ 用于 y=eq，再减去 1 并乘以 q。

### 463.8 收敛到原 A 的严格递增下界

定义完整递归下界

$$
\boxed{\quad
L_n=\mathcal J(B_n)+\mathcal F(r_n,m_n)
=-\int\log v\,B_n(v)\,dv+r_n\log(r_n/m_n).
\quad}
\tag{RVF.32}
$$

**定理 463.8（严格递增与准确极限）。** 对全部 n≥0，

$$
L_0=k\log k,\qquad L_n<L_{n+1}<A,\qquad L_n\longrightarrow A.
\tag{RVF.33}
$$

更准确地，整个无穷轴上的剩余误差满足

$$
\boxed{\qquad 0<A-L_n\le\ell_n+\frac{m_n}{e}\longrightarrow0.\qquad}
\tag{RVF.34}
$$

**证明：每一步的严格下界与极限。** 原 A 身份和完整积分线性性给
$A=\mathcal J(B_n)+\mathcal J(R_n)$。
RVF.29 对真实 Rn 的严格性成立于每个有限 n，包括 R0=B；
RVF.26 已支付全部矩且 Rn 在整个正轴严格正。因此
$A-L_n=\mathcal J(R_n)-\mathcal F(r_n,m_n)>0$。
又 $|\mathcal J(R_n)|\le\ell_n$，RVF.31 给
$A-L_n\le\ell_n+m_n/e$，这就是 RVF.34。
RVF.26 使右侧趋零，故 Ln 趋于同一个原 A。
等价地，$-m_n/e\le\mathcal F(r_n,m_n)<\mathcal J(R_n)\le\ell_n$
把看似可能奇异的剩余项 $r_n\log(r_n/m_n)$ 夹至零，
不需要假定 rn/mn 的极限。n=0 的 B0=0、r0=k、m0=1 给 L0。

**证明：全部有限 n 的严格改进。** RVF.25 与线性性给精确差式

$$
\begin{aligned}
L_{n+1}-L_n
={}&\underbrace{\mathcal J(D_n)-\mathcal F(z_n,t_n)}_{>0}\\
 &+\underbrace{\mathcal F(r_{n+1},m_{n+1})
       +\mathcal F(z_n,t_n)-\mathcal F(r_n,m_n)}_{\ge0}.
\end{aligned}
\tag{RVF.35}
$$

第一项由新增层 Dn 的完整严格 Jensen 支付；第二项由 RVF.30 和
RVF.25 支付。Dn 在正轴处处严格正，所以即使第二项恰好为零，
第一项仍严格正。这支付每一个有限 n 的严格改进。证毕。

### 463.9 保留完整尾的显式收敛误差

**定理 463.9（完整显式误差）。** 对任意 n≥0、V≥1，

$$
\begin{aligned}
\ell_n\le{}&c_n\left[
 \frac1{(3n+1)^2}
 +\frac{\log V\,(V^{3n+1}-1)}{3n+1}\right]
 +C(V+1)e^{-V},\\
m_n\le{}&\frac{c_nV^{3n+2}}{3n+2}+C(V+1)e^{-V}.
\end{aligned}
\tag{RVF.36}
$$

因而

$$
\begin{aligned}
0<A-L_n\le{}&c_n\left[
 \frac1{(3n+1)^2}
 +\frac{\log V\,(V^{3n+1}-1)}{3n+1}
 +\frac{V^{3n+2}}{e(3n+2)}\right]\\
 &+C(V+1)(1+1/e)e^{-V}.
\end{aligned}
\tag{RVF.37}
$$

特别地，令 $q=e^3/81<1/3$。对每个 n≥1 取 V=n，得到

$$
\boxed{\begin{aligned}
0<A-L_n\le{}&\frac{q^n}{2}\left[
 \frac1{(3n+1)^2}
 +\frac{n\log n}{3n+1}
 +\frac{n^2}{e(3n+2)}\right]\\
 &+C(n+1)(1+1/e)e^{-n}.
\end{aligned}}
\tag{RVF.38}
$$

这是同一原 A 的完整轴误差；右侧每一项都有准确的来源。

**证明。** RVF.3 与 RVF.19 同时给

$$
0\le R_n(v)\le\min\{c_nv^{3n},Ce^{-v}\}\quad(v>0).
\tag{RVF.39}
$$

把绝对对数积分分成 (0,1)、[1,V] 与 (V,∞)。第一段用准确积分
$\int_0^1(-\log v)v^{3n}dv=1/(3n+1)^2$；第二段用
$\log v\le\log V$；第三段用 $\log v\le v$ 和
$\int_V^\infty ve^{-v}dv=(V+1)e^{-V}$。这给 RVF.36 第一行。
一阶矩在 (0,V) 使用幂界，在 (V,∞) 使用同一完整指数尾，给第二行。
代入 RVF.34 得 RVF.37。

经典阶乘界 $N!\ge(N/e)^N$ 可由
$\log(N!)\ge\int_1^N\log x\,dx=N\log N-N+1$ 直接得到。
对 N=3n、n≥1 使用它，得

$$
c_n\le\frac{q^n}{2n^{3n}}.
$$

将 V=n 代入 RVF.37，使用 $n^{3n}\ge1$ 并在中段舍去负的 −1，
逐项得到 RVF.38。经典 e<3 给 $q<27/81=1/3$；例如指数级数与
$j!\ge2^{j-1}$（j≥1，j=3 时严格）给
$e=1+\sum_{j\ge1}1/j!<1+\sum_{j\ge1}2^{1-j}=3$。
几何衰减压过括号内的多项式和对数增长，另一完整尾项也趋零。
没有截断后丢掉尾部。证毕。

### 463.10 固定指数族、第二层底座与递归的严格包含

递归的正性还准确连接 §462 的抽底座办法。
对 $0\le\alpha\le1/2$，置 $R_\alpha=B-\alpha e^{-v}$。
RVF.3 支付其完整严格正性，经典 Gamma 对数积分支付
$\mathcal J(\alpha e^{-v})=\alpha\gamma$，故完整严格 Jensen 给

$$
A>G(\alpha):=\alpha\gamma+(k-\alpha)
 \log\frac{k-\alpha}{1-\alpha}.
\tag{RVF.40}
$$

这里的剩余完整质量为 k−α>0、一阶矩为 1−α>0，绝对对数可积性
由 B 与指数核支付。写 $u=(k-\alpha)/(1-\alpha)>0$，直接求导得

$$
G'(\alpha)=\gamma+u-1-\log u>0.
\tag{RVF.41}
$$

$\log u\le u-1$ 和 γ>1/2 支付严格性。因此该固定指数族在 α=1/2
取最强端点，即 §462 的下界。任何常系数完整底座
$\alpha e^{-v}\le B(v)$ 的 v↓0 极限都要求 α≤B(0)=1/2；
α=1/2 已由 RVF.3 实现，故这个系数端点也准确最优。

RVF.8 还给 $p(s)>s^3/3$ 对每个 s>0 成立：被积函数中
$e^t+e^{-t}>2$ 对 t>0 成立，三次积分的其余权重在内部严格正。
于是 $a(s)>e^{-s}/3$，从 b 的准确有限积分得到

$$
B(v)>b(v)>b_2(v):=\frac56e^{-v}-\frac13e^{-2v}
>\frac12e^{-v}>0\qquad(v>0).
\tag{RVF.42}
$$

其中 $b>b_2$ 使用 $a(s)(1+s)>e^{-s}/3$ 并从 0 积分；
$b_2-e^{-v}/2=\frac13(e^{-v}-e^{-2v})>0$。
B>b 是实际 TB 的严格正性。
完整两指数核的准确矩为

$$
\int b_2=\frac23,\qquad \int vb_2=\frac34,\qquad
\mathcal J(b_2)=\frac23\gamma-\frac16\log2.
\tag{RVF.43}
$$

对数矩使用经典完整 Gamma 身份
$\int\log v\,e^{-\lambda v}dv=(-\gamma-\log\lambda)/\lambda$（λ>0）；
这由 w=λv 的换元和 §462 的 λ=1 完整绝对可积积分直接得到。
$R_2^*=B-b_2$ 在整个正轴严格正，完整质量 $r=k-2/3>0$、一阶矩 1/4。
r 的正性来自实际正剩余的积分。严格 Jensen 因而给

$$
A>H_2:=\frac23\gamma-\frac16\log2+r\log(4r).
\tag{RVF.44}
$$

该下界有统一的严格正数值储备：

$$
H_2>\frac13-\frac18-\frac3{32}=\frac{11}{96}.
\tag{RVF.45}
$$

具体地，γ>1/2，$e^{3/4}>1+3/4+(3/4)^2/2=65/32>2$
给 log2<3/4；$e>1+1+1/2+1/6=8/3$ 以及
$r\log(4r)\ge-1/(4e)>-3/32$ 给最后一项。
所有积分均完整，数值界不用拟合 k 或 A。

最后，两底座之间的差 b−b2 在正轴严格正，且不超过 B，三种完整
可积性均已支付；真实剩余 B−b 同样严格正。
将 RVF.35 的同一个预算分割恒等式用于
$B-b_2=(b-b_2)+(B-b)$，得到 $L_1>H_2$。
再用于 $B-e^{-v}/2=(b_2-e^{-v}/2)+(B-b_2)$，得到
$H_2>G(1/2)$。因而这条包含链准确为

$$
\boxed{\quad
L_0<G(1/2)<H_2<L_1<L_2<\cdots<A,\qquad
L_n>\frac{11}{96}\quad(n\ge1).
\quad}
\tag{RVF.46}
$$

固定指数底座、显式两指数底座和原曲率递归在同一个 B 上给出
逐层严格加强；每一步都保留相应完整剩余矩。

### 463.11 剩余散度、隐含关系与 Robin 供应边界

每个有限剩余都定义两份完整正轴概率律

$$
\mu_n(dv)=\frac{R_n(v)}{r_n}\,dv,\qquad
\nu_n(dv)=\frac{vR_n(v)}{m_n}\,dv.
$$

两者相互绝对连续，$d\nu_n/d\mu_n=(r_n/m_n)v$。
RVF.26 的绝对对数可积性支付完整 log 似然比，因而

$$
\boxed{\qquad A-L_n=r_nD_{\rm KL}(\mu_n\Vert\nu_n)>0.\qquad}
\tag{RVF.47}
$$

这只是准确积分身份：展开右侧就是
$-\int\log v\,R_n-r_n\log(r_n/m_n)$。
它把剩余负对数矩、按变量加权的概率律和递归下界连在同一真实密度上。
RVF.35 进一步把每次改进准确拆成新增正层内部的严格 Jensen 缺口，
以及合并两个质量—一阶矩预算时的非负 log-sum 缺口。
因此“正分层—保留剩余矩—严格改进”具有同一原对象的精确恒等式。

这里获得正 Laplace 表示的是递归系数 a；实际 B 由正 Volterra
分层恢复。原 Φ 的既有高阶导数障碍仍适用，未由 RVF.9 改写。
原 Robin 配对的同源 Möbius 谱供应、完整有符号尾控制和最终符号
仍是另需支付的算术桥梁。实际 Fibonacci 完整尾运输及其递归结构
可以提供比较思路，但本节没有给出从这些对象到真实 Möbius 尾的传输定理。
RVF.33、RVF.38 和 RVF.46 提供的是原 A 的完整解析储备与显式逼近。

### 463.12 来源与证明范围

原曲率、原 A、完整矩和指数底座复用 §§444、450、462 及
PrimePrefixPhiCurvature、PrimePrefixOriginalA、PrimePrefixCurvatureMoments。
Gamma 对数积分保持 §462 所述 Mertens.Gamma、PrimeNumberTheoremAnd
端口及 Mathlib Gamma 导数定理的来源。FTC、有限 Fubini、DCT、
严格 log 切线、log 凹性、Taylor 积分余项和阶乘界是经典工具。

本节由同一原曲率的正系数积分表示与三角域算子结构导出
严格递增的完整对数矩下界及明确无穷尾误差。
本节的局部新推导不作全球文献首创声明。
上述递归关系、严格改进及误差界均由同一实际曲率的完整积分导出。

## 追加锚（本行以下为增补区）

### 464 最新 Lean 供应与原 Robin 尾项的有向 Abel 接口

本节接续 §463 的同一原曲率、原常数 A 和实际有符号尾。
2026-10-07 的库检索得到四类准确供应。库名、README 或上游 CI
本身不支付本题的原对象匹配、完整尾项或新工具链上的 kernel 验收。

#### 464.1 可消费的供应及其边界

OpenAI/math 的不可变修订
[`adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a)
在 `lean/OAI/Analysis/VlasovMaxwell/Regularity/VolterraSup.lean`
给出 `OAI.RVM.integral_Icc_factorial_tail`。对所有实数 C、自然数 d
和 t≥0，其准确合同是

$$
C\int_{[0,t]}\frac{(Cu)^d}{d!}\,du
=\frac{(Ct)^{d+1}}{(d+1)!}.
\tag{RLB.1}
$$

这条供应不要求 C≥0；用于正积分比较时另支付 C≥0。
同文件的 `volterra_uniform_bound` 则要求非负 D、C、每个窗口上的
实际有限上界和真实积分递推不等式。其前置
`Retarded/VolterraMajorant.lean` 构造连续单调的全局 majorant。
这些是经典 Volterra 工具；两个小文件只依赖 Mathlib，适合按 Apache-2.0
保留来源后移植所消费的私有证明。上游 Lean 为 4.34.1；本库保持
自身钉版工具链，移植后的实际编译另验。

RLB.1 的自然消费是规范化单项式 v^d/d!。原 T 的内层 lift 增加
两个积分次数，外层增加一个，因此每次真实递归是 d→d+3。
系数 a≤1/3 和 exp(−v)≤1 另给每层的 1/3。这正是 §463 中
`v^(3n)/(2·3^n·(3n)!)` 的结构，而非把原递归改成别的 n! 模型。
规范化阶乘积分的私有移植由同一实际 T 的归纳证明消费；
完整对数矩和算术有符号尾仍需各自支付，不从紧区间一致收敛推出。

dbsanfte/RiemannGaussian 的不可变修订
[`24444671cee3bf643ff1307909b961a329372a9e`](https://github.com/dbsanfte/RiemannGaussian/tree/24444671cee3bf643ff1307909b961a329372a9e)
在 `RiemannGaussian/MoebiusHarmonicMonotoneTail.lean` 给出保留两端点
的有限 Abel 恒等式，以及实际调和 Möbius 前缀有界时的完整单调权尾界。
其 `abs_sum_moebiusHarmonic_antitone_le` 保留 D<M、权非负、权在
[D+1,M] 递减和全部 n∈[D,M] 上的实际前缀界；结论是
`2·e·b(D+1)`。前缀界仍是输入，不能由该尾界反向冒领已经得到消去。

同修订 `MoebiusHarmonicCancellation.lean` 的
`exists_moebiusHarmonicPrefix_cubic_rate` 确实提供实际 H 的统一衰减：

$$
\exists h_0\ge22\ \forall h\ge h_0\ \forall D\in\mathbb N:\quad
e^{2\cdot10^{15}h^3}\le D
\Longrightarrow |H(D)|\le C_{\rm harmonic}e^{-h/8}.
\tag{RLB.7}
$$

其中 h₀、h∈ℝ，C_harmonic=6+4 C_finite 是上游证明为正的固定实常数，
不依赖 h 或 D。
因此满足该阈值的同一 D 对全部后继 n∈[D,M] 支付 Abel 的
前缀小量输入；这不是任意序列上的假设。上游实际 exact-head CI
构建成功，本次尚未将该证明闭包移植并在本库 kernel 验收。
消去率随 log D 的立方根衰减，保留了巨大的准确阈值。
其原核 variation、odd/full 运输和临界归一化仍须独立支付。

AlexKontorovich/PrimeNumberTheoremAnd 的不可变修订
[`c39a751132c88b6e8080b74c74023fd95b3d8be0`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/c39a751132c88b6e8080b74c74023fd95b3d8be0)
在 `PrimeNumberTheoremAnd/StrongPNT.lean` 的 `StrongPNT` 给出

$$
\exists c>0:\qquad
\psi(x)-x=O\!\left(xe^{-c\sqrt{\log x}}\right).
\tag{RLB.2}
$$

这比本库已有 MediumPNT 的对数指数 1/10 更强。
它可补无条件背景尾估计，但尚不直接供给临界平方根消去。
对固定 c>0，令 y=√log x，比较尺度满足

$$
\frac{xe^{-c\sqrt{\log x}}}{\sqrt{x}/\log x}
=y^2e^{y^2/2-cy}\longrightarrow\infty.
\tag{RLB.3}
$$

因此仅从 RLB.2 的上界不能推出本题所需的该临界量级。
上游 StrongPNT 的直接对象也是 ψ；真实 Möbius 权运输仍须单独证明。

OVVO-Financial/mobius-synthesis 的不可变修订
[`516191483bd7c3f82e0e3891c8e1f7266063c335`](https://github.com/OVVO-Financial/mobius-synthesis/tree/516191483bd7c3f82e0e3891c8e1f7266063c335)
包含从实际 Mertens 能量界及平方前缀能量界通往 Mathlib RH 的条件桥。
可复用的是准确归约和对象匹配方式；全尺度能量合同仍是其假设。
有限范围验证不支付全尺度假设，本节也未证明该假设。

#### 464.2 完整有限 Abel 式可以保留单向符号信息

令 μ 为标准算术 Möbius 函数，

$$
H(n)=\sum_{1\le k\le n}\frac{\mu(k)}k,
\qquad Q_D(n)=H(n)-H(D).
$$

对自然数 D<M 和任意实权 b，已读上游合同给出

$$
\begin{aligned}
S_{D,M}(b)
&:=\sum_{D<n\le M}\frac{\mu(n)}n b(n)\\
&=b(M)H(M)-b(D+1)H(D)\\
&\quad-\sum_{D<n\le M-1}[b(n+1)-b(n)]H(n).
\end{aligned}
\tag{RLB.4}
$$

把 H(n)=Q_D(n)+H(D) 逐项代入，有限望远镜身份

$$
\sum_{D<n\le M-1}[b(n)-b(n+1)]=b(D+1)-b(M)
$$

使所有 H(D) 项准确抵消，得到

$$
\boxed{\quad
S_{D,M}(b)=b(M)Q_D(M)
+\sum_{D<n\le M-1}[b(n)-b(n+1)]Q_D(n).
\quad}
\tag{RLB.5}
$$

这里没有删除终端项 b(M)Q_D(M)。当 M=D+1 时内和为空，
RLB.5 就是单个真实 Möbius 项，端点同样成立。

若 b 在 [D+1,M] 非负递减，RLB.5 中全部系数非负，系数总和
准确等于 b(D+1)。故只要同一区间实际满足
`Q_D(n)≥−e`（D<n≤M，e≥0），就有

$$
S_{D,M}(b)\ge-e\,b(D+1).
\tag{RLB.6}
$$

证明是分别以非负系数乘这个下界，再用有限望远镜求和。
它保持单向目标；并不额外要求 Q_D 的上界。若 b(D+1)>0，
`S/b(D+1)` 是这些实际有向前缀差的一个凸组合。
若 b(D+1)=0，非负递减使整段 b 都为零，S=0。
若只知道原 H 在 [D,M] 满足 |H|≤e，则 |Q_D|≤2e，
这解释上游完整绝对值尾界的因子 2。更强的有向前缀差输入
可以避免先取绝对值造成的这一信息损失。

若原 H 的后继统一界是 |H(n)|≤δ，保留准确锚 H(D) 还给

$$
Q_D(n)\ge-\delta-H(D),\qquad
S_{D,M}(b)\ge-[\delta+H(D)]b(D+1).
\tag{RLB.8}
$$

这里 δ+H(D)≥0 由同一 D 上的界支付。当 H(D)<0 时，
这个准确有向预算比先把 H(D) 替成 |H(D)| 再合并的 2δ 更小。
RLB.7 确实在其存在阈值以后对所有后继 n 同时提供
δ=C_harmonic exp(−h/8)。其 h₀ 仍是存在常数；这条供应
不自行给出一个可枚举的有限阈值或本题最终符号。

RLB.5–6 是从完整有限 Abel 合同和望远镜身份得到的经典推论，
不作新的文献优先权声明。本节给出它们的完整有限证明；
尚未把它们绑定并冻结为本库原 Robin 核的正式结果。

#### 464.3 与正递归的联系及准确缺口

§463 的正算子 T 从实际曲率的正残差生成下一层正残差。
RLB.5 则让非负递减权作用于实际算术前缀差 Q_D。
两者都允许保留输入的一个方向，但所作用的对象不同：
前者的正性来自已经证明的解析积分；后者需要真实 Möbius
前缀差的有向下界。RLB.5 没有把 μ 本身变成非负系数。

原 Robin 配对若要消费 RLB.6，必须支付同一索引和截断下的
准确权重身份、非负递减域、全部有向前缀差下界及完整终端项。
若原权不单调，则仍使用 RLB.5 的有符号增量，而不能套用 RLB.6。
有限公式也不自行准许无限重排或交换极限与积分。
这把下一步供应需求具体化为原核上的有向前缀运输，
而不是继续扩大已经为正的 A 储备来替代算术消去。

Fibonacci 的递归和原曲率的三重积分递归可帮助发现合适的
分层语言。它们不提供 μ 的真实相位，也不自动证明上述有向前缀差界。
5040 是 Robin 定理中已知有限例外范围的最后整数边界；
本节没有从 7!、Fibonacci 索引或拓扑染色例外推导算术尾控制。

OpenAI/math 同修订还公开了一个声称 `Re(s)>7/8` 时实际 ζ 不为零
的入口。其源码及显式 import 闭包已作静态检查；尚无本次对该完整
闭包的实际 kernel 验收。它不参与本节或本库 RH 结论的承重推导。
上述小供应的移植各自按本库钉版真实编译；RH 和原 Robin 全尾
的最终符号仍保持开放。


## 追加锚（本行以下为增补区）

## 465. 完整剩余预算与有向前缀运输

本节沿用同一个实际函数 Φ、曲率 B=Φ''、正递归 Bₙ 及残差 Rₙ=B−Bₙ。令 C=e^γ、k=C−1。既有完整轴恒等式为 ∫₀∞B=k、∫₀∞vB=1、A=−∫₀∞log(v)B(v)dv。这里的 A 始终是原解析主项；算术 Möbius 尾的符号须另行支付。

#### 465.1 尾积分的精确剩余量

**命题 465.1（同一曲率的完整尾）。** 对每个 V≥0，定义

$$
Q(V)=\int_V^\infty B(v)\,dv,\qquad
M(V)=\int_V^\infty vB(v)\,dv.
$$

这些积分绝对可积，且

$$
Q(V)=C-\Phi'(V),\qquad
M(V)=\Phi(V)-V\Phi'(V)=\Phi(V)e^{-V},
\qquad 0<M(V)\le e(1+V)e^{-V}.
\tag{RB.1}
$$

对 V≥1，完整绝对对数尾满足

$$
0\le\int_V^\infty|\log v|B(v)\,dv\le M(V),
\tag{RB.2}
$$

M(V) 及 RB.2 的完整绝对对数尾都趋于零。V=0 同样包含在 RB.1 中：Q(0)=k、M(0)=1。

证明由有限区间微积分与已有全轴可积性得 Q(V)；对 vB 分部积分给 M(V)=Φ(V)−VΦ'(V)。同一 Φ 的微分身份 VΦ'(V)=(1−e⁻ⱽ)Φ(V) 给最后一个等号，V=0 由 Φ(0)=1 直接支付。原上界 Φ(V)≤e(1+V) 给指数包络。V≥1 时 0≤log v≤v，逐点比较得到 RB.2。

RB.1 给出另一个读法：正轴上的 vB(v)dv 是总质量为 1 的实际正测度，M(V) 正是其剩余质量。这个读法使用已支付的一阶矩，不能把 B 本身误归一成总质量 1。

#### 465.2 递归对完整轴的恢复

**命题 465.2（实际残差的完整矩消失）。** 令 Dₙ=Bₙ₊₁−Bₙ，并定义

$$
r_n=\int_0^\infty R_n(v)\,dv,\quad
m_n=\int_0^\infty vR_n(v)\,dv,\quad
\ell_n=\int_0^\infty|\log v|R_n(v)\,dv.
$$

Bₙ、Rₙ、Dₙ 的质量、一阶矩及对数矩均可积；Rₙ 另有完整绝对对数矩。每个有限 n 上 rₙ>0、0<mₙ≤1，Dₙ 的质量和一阶矩也严格为正，并有准确分裂

$$
r_n=r_{n+1}+\int_0^\infty D_n(v)\,dv,\qquad
m_n=m_{n+1}+\int_0^\infty vD_n(v)\,dv.
\tag{RB.3}
$$

同时 rₙ→0、mₙ→0、ℓₙ→0，且 ∫₀∞log(v)Rₙ(v)dv→0。

证明使用原严格递归的 0<Rₙ≤B、0<Dₙ≤Rₙ、0≤Bₙ≤B，以及 §464 的实际残差逐点趋零。三个主导函数分别是 B、vB 和 |log v|B，均在完整正轴可积。分别应用主导收敛，最后用 |∫log(v)Rₙ|≤ℓₙ 支付有符号对数矩。这里需要完整主导；紧区间一致收敛本身不能代替这一步。严格正预算也表明任何有限层尚有剩余，极限恢复须另由收敛证明。

#### 465.3 离散尾怎样消费正预算

**命题 465.3（真实 Möbius 前缀差的有限运输）。** 令 H(N)=Σ₁≤ⱼ≤ᴺ μ(j)/j，Q_D(n)=H(n)−H(D)。对自然数 D<M 及任意实权 b，有限尾满足

$$
\sum_{D<n\le M}\frac{\mu(n)}n b(n)
=b(M)Q_D(M)
 +\sum_{D<n\le M-1}[b(n)-b(n+1)]Q_D(n).
\tag{RB.4}
$$

若 b 在 [D+1,M] 非负递减，且 Q_D(n)≥−ε 对全部 D<n≤M 成立、ε≥0，则

$$
\sum_{D<n\le M}\frac{\mu(n)}n b(n)\ge-\varepsilon b(D+1).
\tag{RB.5}
$$

若改用含锚 D 的统一输入 |H(n)|≤δ（D≤n≤M），则 δ+H(D)≥0，并得到保留准确锚的更具体预算

$$
\sum_{D<n\le M}\frac{\mu(n)}n b(n)
\ge-[\delta+H(D)]b(D+1).
\tag{RB.6}
$$

证明是有限分部求和与望远镜相消。RB.4 中系数均非负，系数总和恰为 b(D+1)，所以逐项乘有向下界得 RB.5；Q_D(n)≥−δ−H(D) 给 RB.6。终端 b(M)Q_D(M) 全程保留。M=D+1 时内和为空；b(D+1)=0 时非负递减强制整段权为零，尾和也为零。

在上述非负递减条件下且 b(D+1)>0 时，RB.4 除以 b(D+1) 就是实际前缀差的一个凸组合。它与 RB.1 的概率读法共享“非负系数及其准确总量”这一结构，但输入分别是曲率密度和算术前缀差；它们之间的实际对象桥尚须证明。

#### 465.4 五分类、递归与下一供应接口

RB.3 的预算向量 (r,m) 按逐层正块相加。有限分类可视为给同一预算增加分块；有效改进须来自块的真实正性、矩和误差控制。正预算加法有交换律与结合律，但非零正预算没有同域加法逆元，因而不能把这个结构直接称为群。分类数 5 本身不支付消去估计。

外部 Gaussian 库的调和 Möbius 前缀衰减能提供 RB.6 所需的一类输入；本节的有限运输并未移植其完整衰减证明。要作用到原 Robin 有符号尾，仍须识别同一截断下的实际权 b，证明其非负递减性或支付准确变差，处理 odd/full 前缀转换，并保留无限极限的全部终端。一般素数定理或解析正储备都不能直接替代这些合同。

5040=7!、Fibonacci 递归和拓扑例外可以提出比较问题。本节实际闭合的是完整曲率剩余预算及有限 Möbius 运输；没有从数字 7、分类数 5 或 Fibonacci 原子推出 Robin 的无限判据。

## 追加锚（本行以下为增补区）

## 466. 奇调和 Möbius 的有限收缩与原增长权的完整变差

本节接续 §§464–465 的实际调和前缀与 §§453–455 的原阶乘核。
先证明准确有限收缩，再在实际奇调和衰减假设下控制原增长权。
固定 x 的尾存在性与同时增长尺度下的 Robin 临界符号须分别支付。

#### 466.1 同一去素数 2 操作的准确有限递归

保持标准算术 Möbius 函数 μ，令

$$
H(N)=\sum_{1\le n\le N}\frac{\mu(n)}n,
\qquad H_{\mathrm o}(N)=
\sum_{\substack{1\le n\le N\\n\text{ 奇}}}\frac{\mu(n)}n,
\qquad H(0)=H_{\mathrm o}(0)=0.
$$

**命题 466.1（两个准确有限身份）。** 对全部自然数 N、K，

$$
\boxed{H(N)=H_{\mathrm o}(N)
-\frac12H_{\mathrm o}(\lfloor N/2\rfloor),}
\tag{HG.1}
$$

$$
\boxed{H_{\mathrm o}(N)
=\sum_{a=0}^{K-1}2^{-a}H(\lfloor N/2^a\rfloor)
+2^{-K}H_{\mathrm o}(\lfloor N/2^K\rfloor).}
\tag{HG.2}
$$

这里 K=0 时和为空；HG.2 的末项为原 H_o(N)，身份同样成立。

**证明。** 将 H(N) 的有限整数集合拆为奇数与偶数。
每个偶数 n 唯一写成 n=2m，端点准确为
1≤m≤⌊N/2⌋。奇数 m 与 2 互素，Mathlib 的实际 μ 乘法性及
μ(2)=−1 给 μ(2m)=−μ(m)；偶数 m 时 4∣2m，所以
μ(2m)=0。因而包括全部偶端点的和恰为

$$
\sum_{m=1}^{\lfloor N/2\rfloor}\frac{\mu(2m)}{2m}
=-\frac12\sum_{\substack{m\le\lfloor N/2\rfloor\\m\text{ 奇}}}
\frac{\mu(m)}m.
$$

加入原奇数部分就是 HG.1；N=0 时两部分都为空。

HG.2 对 K 作归纳。K=0 已说明。若 K 层身份成立，
将其末项里的 H_o(⌊N/2^K⌋) 依 HG.1 改写为

$$
H(\lfloor N/2^K\rfloor)
+\frac12H_{\mathrm o}(\lfloor N/2^{K+1}\rfloor).
$$

这里整数除法恒等式
⌊⌊N/2^K⌋/2⌋=⌊N/2^(K+1)⌋ 保留准确截止。
乘原 2^(−K) 后，第一项加入有限和的 a=K 项，
第二项正是 K+1 层末项，归纳完成。

取 K=N+1，初等归纳给 2^(N+1)≥N+2>N，
所以最后一个整数商为零，末项准确消失。
那些满足 2^a>N 的和项也为 H(0)=0。
全程是有限重索引与有限代入，没有使用无限级数重排。证毕。

§453 的同一原始前缀满足
M(N)=O(N)−O(⌊N/2⌋)，其中 O 为未加权的实际奇 Möbius 前缀。
其递归系数是 1；把同一整数系数乘以实际倒数指标后，
HG.1 的系数变为 1/2。HG.2 因而给出有限几何权，
其总量准确为 2(1−2^(−K))≤2，末项系数为 2^(−K)。
这是去素数 2 与调和权之间的真实收缩关系。
它说明选择不同但准确匹配的权会改变递归运输的成本；
算术 μ 的符号与小指标末项仍须保留。

#### 466.2 原 Robin 的增长权

保持 §§453–455 的全部原对象，对实数 x≥e、s>0，

$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad w(t)=\frac{1+\log t}{t^2\log^2t},
$$

$$
P_x^\eta(s)=\int_x^\infty\eta(t/s)w(t)\,dt,
\qquad\mathscr D_x(s)=P_x^\eta(s)-P_x^\eta(2s),
\qquad b_x(s)=s\mathscr D_x(s).
\tag{HG.3}
$$

实际奇来源逐项满足
μ(n)𝒟_x(n)=[μ(n)/n]b_x(n)。这只是同一完整核的准确换权。
固定 x，记 ℓ=log x、r=log s、L=log 2，设

$$
c_x=\ell^{-1}-\log\ell-1,
\qquad d_x=\ell^{-1}+\ell-1.
$$

§453 的 DP.9–DP.10 给 s≥x 时

$$
sP_x^\eta(s)=r\log r+c_xr+d_x-r^{-1}+E_x(r),
\qquad |E_x(r)|\le2(r^{-1}+r^{-2}).
\tag{HG.4}
$$

将 r+L 的同一身份减去一半，使用
(r+L)log(r+L)=r log r+L log r+L+O(r^(−1))，得

$$
b_x(s)=\frac12r\log r+\frac12c_xr
-\frac L2\log r+\frac12d_x-\frac L2(c_x+1)+O_x(r^{-1}).
\tag{HG.5}
$$

故 b_x(s)→+∞。§465 非负递减权的完整尾比较不能直接用于这个
全部远端权；这里需要完整变差。

该变差不从 HG.5 的渐近猜测导数。复用 §453 的 DP.4：
s>x 时 −(P_x^η)'(s)=G_{η,x}(log s)/s²，且对 v=log(s/x)≥0，
|ℓG_{η,x}(ℓ+v)|≤v²/2+v+12。
此 G_{η,x} 为原核变换，区别于 H_o。
令

$$
K_x=6+|c_x|+|d_x|,\qquad V_x=3K_x+39.
$$

r≥ℓ≥1 时 HG.4 给 |P_x^η(s)|≤K_x(1+r)²/s；
同一个导数界给 |(P_x^η)'(s)|≤13(1+r)²/s²。
在 2s 使用 1+log(2s)≤2(1+log s)，并对 HG.3 求导，得到

$$
\boxed{|b_x(s)|\le3K_x(1+\log s)^2,
\qquad |b'_x(s)|\le V_x\frac{(1+\log s)^2}{s}\quad(s>x).}
\tag{HG.6}
$$

这些常数明确允许依赖固定 x。HG.6 依赖同一原核的完整可积性和
求导身份，不能通过对 HG.5 的渐近余项直接求导得到。

#### 466.3 固定 x 的完整变差合同与临界边界

**命题 466.2（实际奇来源的条件尾合同）。** 固定 x≥e。
令整数 D>x，另行支付实际奇调和前缀的准确全后继合同

$$
|H_{\mathrm o}(n)|\le C_{\mathrm o}
 e^{-c_{\mathrm o}(\log n)^{1/3}}\quad(n\ge D),
\qquad C_{\mathrm o}\ge0,\ c_{\mathrm o}>0.
\tag{HG.7}
$$

则同一原奇来源的自然截止尾存在。
写 c=c_o，z₀=(log(D+1))^(1/3)，并定义完整积分

$$
J_j(c,z_0)=\int_{z_0}^\infty z^j e^{-cz}dz
=e^{-cz_0}\sum_{k=0}^j\frac{j!}{k!c^{j-k+1}}z_0^k,
\qquad j\in\mathbb N.
\tag{HG.8}
$$

其准确锚与完整预算为

$$
\begin{aligned}
\mathscr T_{D,\infty}(x)
&=-b_x(D+1)H_{\mathrm o}(D)
-\sum_{n=D+1}^\infty[b_x(n+1)-b_x(n)]H_{\mathrm o}(n),\\
|\mathscr T_{D,\infty}(x)|
&\le |b_x(D+1)|\,|H_{\mathrm o}(D)|\\
&\quad+3C_{\mathrm o}V_xe^c
 [J_2(c,z_0)+2J_5(c,z_0)+J_8(c,z_0)].
\end{aligned}
\tag{HG.9}
$$

**证明。** 对 M>D，有限 Abel 恒等式给同一奇来源尾

$$
\begin{aligned}
\mathscr T_{D,M}(x)
&:=\sum_{\substack{D<n\le M\\n\text{ 奇}}}\mu(n)\mathscr D_x(n)\\
&=b_x(M)H_{\mathrm o}(M)-b_x(D+1)H_{\mathrm o}(D)\\
&\quad-\sum_{n=D+1}^{M-1}[b_x(n+1)-b_x(n)]H_{\mathrm o}(n).
\end{aligned}
\tag{HG.10}
$$

终端与锚均保留。HG.6–HG.7 给 b_x(M)H_o(M)→0，
因为置 z=(log M)^(1/3) 后只是多项式乘 e^(−cz)。
每个整数单元上，将 b_x 与连续主导函数
V_x(1+log t)²/t 的原函数作导数比较，得到增量的积分界。
对 n≤t≤n+1、n≥1，非负立方根的次可加性给
(log t)^(1/3)−(log n)^(1/3)≤[log(t/n)]^(1/3)<1。
于是整个变差和满足

$$
\begin{aligned}
&\sum_{n=D+1}^\infty
 |b_x(n+1)-b_x(n)|\,|H_{\mathrm o}(n)|\\
&\quad\le C_{\mathrm o}V_xe^c\int_{D+1}^\infty
 e^{-c(\log t)^{1/3}}\frac{(1+\log t)^2}{t}dt\\
&\quad=3C_{\mathrm o}V_xe^c\int_{z_0}^\infty
 e^{-cz}(z^2+2z^5+z^8)dz<\infty.
\end{aligned}
\tag{HG.11}
$$

最后一个等号先用 u=log t，再用 z=u^(1/3)。
完整积分 HG.8 由 J₀=e^(−cz₀)/c 以及保留无穷端点的递推
J_j=z₀^j e^(−cz₀)/c+(j/c)J_(j−1) 得到；
端点 z^j e^(−cz)→0，归纳给其准确有限多项式。
因此 HG.10 中变差级数绝对收敛，终端趋零，
取自然截止极限并用三角不等式就是 HG.9。证毕。

HG.11 只证明 Abel 变差项的绝对可和与原子尾的自然截止存在；
不声称原子和本身绝对收敛。连接 §453 的累计 Mertens 配对时，
仍须支付其准确 clipped 端点，不能借此许可独立的无限素数—合数分拆。

§464 的 Gaussian 供应 RLB.7 给实际完整 H 的立方对数衰减。
HG.2 给从完整 H 到实际 H_o 的准确有限运输，
但其中的小指标末项必须另行估计。
命题 466.2 的结论依赖 HG.7 对实际奇调和前缀的全部后继界；
有限身份本身不提供这个衰减假设。

即使支付了 HG.7，固定 x 的 HG.9 也不自动支付原
√x log x 临界共同精度。对固定 q>1 的整数截止 D=⌈x^q⌉，
即便 C_o 和 K_x 只造成对数因素，
√x 仍压过 exp[−c_o(q log x)^(1/3)]；这个上界本身
无法给出所需共同临界预算。增长更快的来源截止仍留下整个有限头部的
真实符号或消去任务。原 Robin 完整符号和 RH 保持开放。

实际 μ 与有限重索引复用 Mathlib 及 §453 的
ActualOddMobiusFinitePairing；Abel 代数保持 Mathlib 的来源。
Gaussian 的不可变修订 24444671cee3bf643ff1307909b961a329372a9e
及完整 Apache-2.0 归属见
[原调和 Abel 来源记录](../../../Library/Analytic/sanftenberg2026harmonicabel.md)。
本节有限收缩和固定尺度变差推导不提出文献优先权主张。

## 追加锚（本行以下为增补区）

## 467. 同一原 A 的残差、size-bias 与分类链律

本节保留 §§463–465 的同一实际函数 $\Phi$、曲率 $B=\Phi''$、递归 $B_n$ 和残差 $R_n=B-B_n$。以下积分均在完整正轴 $(0,\infty)$ 对 Lebesgue 测度进行。本节把同一原 $A-L_n$ 绑定到实际残差的相对熵，并把真实递归的四个新增层与剩余尾项组成五类。

#### 467.1 原完整误差的概率读法

令 $C=e^\gamma$、$k=C-1>0$，保持同一个原完整常数

$$
\begin{aligned}
A
&=\int_0^1\frac{\Phi(v)(1-e^{-v})-v}{v^2}\,dv
 +\int_1^\infty\left[\frac{\Phi(v)(1-e^{-v})}{v^2}-\frac C v\right]dv\\
&=-\int_0^\infty\log(v)B(v)\,dv.
\end{aligned}
\tag{RSK.1}
$$

§465 给每个自然数 $n$ 的完整预算

$$
r_n=\int_0^\infty R_n(v)\,dv>0,\qquad
m_n=\int_0^\infty vR_n(v)\,dv>0,\qquad
\ell_n=\int_0^\infty|\log v|R_n(v)\,dv<\infty.
$$

实际 $R_n(v)>0$ 对每个 $v>0$ 成立。定义同一完整下界

$$
L_n=-\int_0^\infty\log(v)B_n(v)\,dv
      -r_n\log(m_n/r_n),
\qquad \mu_n=m_n/r_n.
\tag{RSK.2}
$$

**命题 467.1（实际残差与其 size-bias 的完整相对熵）。** 对全部自然数 $n$，定义正轴上的密度

$$
p_n(v)=\frac{R_n(v)}{r_n},\qquad
q_n(v)=\frac{vR_n(v)}{m_n}.
\tag{RSK.3}
$$

二者都是概率密度，且 $q_n=vp_n/\mu_n$，即 $p_n$ 的 size-bias 密度。取自然对数，定义

$$
D(p\Vert q)=\int_0^\infty p(v)\log\frac{p(v)}{q(v)}\,dv.
$$

本命题中该积分绝对可积，并且

$$
\boxed{
A-L_n
=r_n D(p_n\Vert q_n)
=\int_0^\infty h(v/\mu_n)R_n(v)\,dv>0,
\qquad h(x)=x-1-\log x.
}
\tag{RSK.4}
$$

在 $n=0$ 时，$R_0=B$、$r_0=k$、$m_0=1$、$L_0=k\log k$，所以

$$
\boxed{A-k\log k=kD(B/k\Vert vB).}
\tag{RSK.5}
$$

**证明。** 完整质量与一阶矩分别给 $\int p_n=1$、$\int q_n=1$。正轴上每个分母都严格正，故逐点有

$$
\frac{p_n(v)}{q_n(v)}=\frac{\mu_n}{v},\qquad
\log\frac{p_n(v)}{q_n(v)}=\log\mu_n-\log v.
$$

完整绝对可积性由已支付的预算直接控制：

$$
\int_0^\infty p_n(v)
 \left|\log\frac{p_n(v)}{q_n(v)}\right|dv
\le |\log\mu_n|+\frac{\ell_n}{r_n}<\infty.
\tag{RSK.6}
$$

这里同时保留零附近和无穷远端，不要求 $R_n\log R_n$ 可积。计算的是对数比的完整积分，没有将两个可能发散的微分熵相减。

由 $B=B_n+R_n$ 及完整对数积分的线性性，RSK.1–RSK.2 给

$$
\begin{aligned}
A-L_n
&=-\int_0^\infty\log(v)R_n(v)\,dv+r_n\log\mu_n\\
&=r_nD(p_n\Vert q_n).
\end{aligned}
$$

另一方面 $h(v/\mu_n)R_n(v)$ 的可积性由 $vR_n$、$R_n$ 和 $|\log v|R_n$ 支付；其线性项的完整积分恰为

$$
\int_0^\infty(v/\mu_n-1)R_n(v)\,dv
=m_n/\mu_n-r_n=0.
$$

展开 $h$ 就得到 RSK.4 的第二个等号。对 $x>0$，对数切线不等式给 $h(x)\ge0$，且 $x\ne1$ 时严格大于零。实际 $R_n$ 在正轴严格正，故在正测度集合 $v>2\mu_n$ 上被积函数严格正，完整积分也严格正。

最后 $B_0=0$、$\int B=k$ 和 $\int vB=1$ 给全部零层预算及 RSK.5。特别是 $B/k$ 与 $vB$ 分别被正确归一化；$B$ 的质量是 $k$。证毕。

RSK.4 的方向是 $p_n\Vert q_n$。若反向取 $q_n\Vert p_n$，其对数期望变成一阶矩加权的 $v\log v$ 积分，须另行支付这一可积性。当前完整误差所消费的是 RSK.6 的已付绝对对数矩。

#### 467.2 同一实际残差的非空有限正分类

**命题 467.2（实际 $R_n$ 的完整分类恒等式）。** 固定任意自然数 $n$，令 $I$ 为非空有限集合。对每个 $i\in I$，设 $f_i$ 是正轴上严格正的可测函数，并且对全部 $v>0$ 有准确分解

$$
\sum_{i\in I}f_i(v)=R_n(v).
$$

不另设各块的矩假设。置

$$
\begin{gathered}
r_i=\int_0^\infty f_i(v)\,dv,\qquad
m_i=\int_0^\infty vf_i(v)\,dv,\qquad
\mu_i=m_i/r_i,\\
p_i=f_i/r_i,\qquad q_i=vf_i/m_i,\\
a_i=r_i/r_n,\qquad b_i=m_i/m_n,
\qquad F(r,m)=-r\log(m/r).
\end{gathered}
$$

则各 $r_i,m_i$ 严格正，各 $f_i$、$vf_i$ 和 $|\log v|f_i$ 在完整正轴可积，且

$$
\sum_{i\in I}r_i=r_n,\qquad \sum_{i\in I}m_i=m_n.
$$

因此 $p_i,q_i$ 都是概率密度，$a,b$ 都是严格正的有限概率向量。全部相对熵均有限，同一原完整误差有准确分类

$$
\boxed{
A-L_n
=\sum_{i\in I}r_iD(p_i\Vert q_i)
  +r_nD(a\Vert b).
}
\tag{RSK.8}
$$

离散项恰为这些实际块的预算合并缺口：

$$
\begin{aligned}
H_I
&:=\sum_{i\in I}F(r_i,m_i)-F(r_n,m_n)\\
&=r_nD(a\Vert b)
=\sum_{i\in I}r_i h(\mu_i/\mu_n)\ge0.
\end{aligned}
\tag{RSK.7}
$$

此项等于零当且仅当各块均值全部等于 $\mu_n$。这些身份涵盖单一类别，且不依赖有限合并的顺序。

**证明。** 每个 $v>0$ 都有 $0<f_i(v)\le R_n(v)$。因而三个非负被积函数分别受已知可积函数支配：

$$
0<f_i\le R_n,\qquad
0<vf_i\le vR_n,\qquad
0\le |\log v|f_i\le |\log v|R_n.
$$

可测性和支配可积性给三份完整积分存在；其中前两者在整个正轴严格正，所以 $r_i,m_i>0$。又
$|\log(v)f_i(v)|=|\log v|f_i(v)$，故有符号对数矩也绝对可积，包含零附近和无穷远两端。有限积分可加性给准确质量和一阶矩预算。各概率密度与有限向量的归一化随之成立。

以下有限相对熵链式公式是经典先例，亦有 §467.4 所引 Mathlib 的一般测度版本；在这里把它用于上述实际 $R_n$ 分解。逐项展开

$$
\log(a_i/b_i)=\log(r_i/m_i)-\log(r_n/m_n),
$$

乘 $r_i$ 后求有限和，得到 RSK.7 的第一个身份。又

$$
\sum_{i\in I}r_i(\mu_i/\mu_n-1)
=m_n/\mu_n-r_n=0.
$$

这给 RSK.7 的 $h$ 身份及非负性；$r_i>0$ 与 $h(x)=0\iff x=1$ 给等号条件。

各块的对数比完整可积，因为

$$
\int_0^\infty p_i(v)
  \left|\log\frac{p_i(v)}{q_i(v)}\right|dv
\le |\log\mu_i|
  +\frac1{r_i}\int_0^\infty|\log v|f_i(v)\,dv<\infty.
$$

令 $J(g)=-\int_0^\infty\log(v)g(v)dv$。对数比的逐点公式给

$$
r_iD(p_i\Vert q_i)=J(f_i)-F(r_i,m_i),\qquad
r_nD(p_n\Vert q_n)=J(R_n)-F(r_n,m_n).
$$

由 $J(R_n)=\sum_iJ(f_i)$ 及 RSK.7，得到经典链式公式在这些实际密度上的身份

$$
r_nD(p_n\Vert q_n)
=\sum_{i\in I}r_iD(p_i\Vert q_i)+r_nD(a\Vert b).
$$

最后代入命题 467.1 的 $r_nD(p_n\Vert q_n)=A-L_n$ 就是 RSK.8。

也可核对两个联合概率密度

$$
P(i,v)=\frac{f_i(v)}{r_n}=a_ip_i(v),\qquad
Q(i,v)=\frac{vf_i(v)}{m_n}=b_iq_i(v).
$$

给定类别 $i$，对数比拆为 $\log(a_i/b_i)+\log(p_i/q_i)$。给定同一 $v>0$，则

$$
P(i\mid v)=\frac{f_i(v)}{R_n(v)}=Q(i\mid v),
\tag{RSK.9}
$$

因为共同因子 $v$ 在归一化中消去。故给定 $v$ 后的类别相对熵为零，联合分布的相对熵恰等于总残差密度的相对熵。

对任意二叉合并树，把每次合并的
$F(\text{左预算})+F(\text{右预算})-F(\text{合预算})$
相加。每个内部节点的 $F$ 在自身合并中出现一次负号、在父节点合并中出现一次正号，准确相消；最后只剩 RSK.7 的 $H_I$。若只有一个类别，$f_i=R_n$，于是 $H_I=0$，RSK.8 退回 RSK.4。证毕。

这里的分类是同一实际残差的全正轴严格正解析块。对不相交单元的零密度分类，须另定义零密度处的对数比；它不包含于本命题的严格正假设。

#### 467.3 实际递归的相对熵收益与五分类

**推论 467.3（实际每一层的相对熵收益）。** 对全部自然数 $n$，令

$$
D_n=B_{n+1}-B_n,\qquad
z_n=\int_0^\infty D_n(v)\,dv>0,\qquad
t_n=\int_0^\infty vD_n(v)\,dv>0.
$$

则实际相邻分裂 $R_n=R_{n+1}+D_n$ 满足

$$
\begin{aligned}
L_{n+1}-L_n
&=z_nD\left(\frac{D_n}{z_n}\,\middle\Vert\,\frac{vD_n}{t_n}\right)\\
&\quad+r_nD\left(
\left(\frac{r_{n+1}}{r_n},\frac{z_n}{r_n}\right)
\,\middle\Vert\,
\left(\frac{m_{n+1}}{m_n},\frac{t_n}{m_n}\right)
\right)>0.
\end{aligned}
\tag{RSK.10}
$$

**证明。** §465 的准确预算分裂给 $r_n=r_{n+1}+z_n$、$m_n=m_{n+1}+t_n$。实际 $R_{n+1}$ 与 $D_n$ 在完整正轴严格正，且准确相加为 $R_n$，因此满足命题 467.2。应用 RSK.8，再用 RSK.4 把剩余块的缺口改写为 $A-L_{n+1}$，与原 $A-L_n$ 相减即得 RSK.10。新增层 $D_n$ 的连续相对熵严格正，证明同命题 467.1 的 $h$ 支撑论证；离散项非负，故实际收益严格正，包括 $n=0$。证毕。

**推论 467.4（四个实际新增层与剩余尾项的五分类）。** 对每个自然数 $n$，同一残差有完整正分解

$$
R_n=D_n+D_{n+1}+D_{n+2}+D_{n+3}+R_{n+4}.
$$

定义五项严格正概率向量

$$
\begin{aligned}
\mathbf a_n
&=\frac{(z_n,z_{n+1},z_{n+2},z_{n+3},r_{n+4})}{r_n},\\
\mathbf b_n
&=\frac{(t_n,t_{n+1},t_{n+2},t_{n+3},m_{n+4})}{m_n}.
\end{aligned}
$$

实际四步下界收益准确为

$$
\boxed{
L_{n+4}-L_n
=\sum_{j=0}^{3}z_{n+j}
 D\left(\frac{D_{n+j}}{z_{n+j}}
 \,\middle\Vert\,\frac{vD_{n+j}}{t_{n+j}}\right)
 +r_nD(\mathbf a_n\Vert\mathbf b_n)>0.
}
\tag{RSK.11}
$$

此外，定义同一准确预算上的逐层合并缺口

$$
H_s:=F(r_{s+1},m_{s+1})+F(z_s,t_s)-F(r_s,m_s).
$$

则它们满足

$$
\boxed{
\sum_{j=0}^{3}H_{n+j}
=r_nD(\mathbf a_n\Vert\mathbf b_n).
}
\tag{RSK.12}
$$

**证明。** 连续应用四次 $R_s=D_s+R_{s+1}$，逐点得到所述五块分解。各块均在正轴严格正，因而命题 467.2 自动支付其质量、一阶矩及完整绝对对数矩；准确预算为

$$
r_n=\sum_{j=0}^{3}z_{n+j}+r_{n+4},\qquad
m_n=\sum_{j=0}^{3}t_{n+j}+m_{n+4}.
$$

对这五块应用 RSK.8。其中尾块贡献
$r_{n+4}D(p_{n+4}\Vert q_{n+4})=A-L_{n+4}$，
把它从 $A-L_n$ 中移去便得到 RSK.11，同一原 $A$ 准确消去。四个新增层的连续项各严格正，预算项非负，所以总收益严格正。

逐层预算合并缺口的准确形式是

$$
H_s=F(r_{s+1},m_{s+1})+F(z_s,t_s)-F(r_s,m_s).
$$

令 $s=n,n+1,n+2,n+3$ 后求和，中间三个剩余预算的 $F$ 正负相消，故

$$
\sum_{j=0}^{3}H_{n+j}
=\sum_{j=0}^{3}F(z_{n+j},t_{n+j})
 +F(r_{n+4},m_{n+4})-F(r_n,m_n).
$$

右边正是这五块的 RSK.7，给 RSK.12。证毕。

五分类与四次二分由此给出同一个离散信息差：前者一次比较五个质量份额与一阶矩份额，后者逐步累加预算合并缺口。连续项比较每个实际层与其 size-bias。分类数五在此表示四个真实剥离层加一份尾项；相同推导适用于任意有限层数。正预算加法的交换、结合性质来自准确求和，正预算域中没有与一般块相加后为零的逆元。

**推论 467.5（加权相对熵的完整极限）。** 同一实际残差满足

$$
0<r_nD(p_n\Vert q_n)
=A-L_n
\le\ell_n+\frac{m_n}{e},\qquad
r_nD(p_n\Vert q_n)\longrightarrow0.
\tag{RSK.13}
$$

**证明。** 命题 467.1 给等号与严格正性。完整对数比公式给

$$
A-L_n=-\int_0^\infty\log(v)R_n(v)\,dv
       +r_n\log(m_n/r_n).
$$

首项不超过 $\ell_n$。令 $x=r_n/m_n>0$，用经典标量不等式 $x\log x\ge-1/e$，得到

$$
r_n\log(m_n/r_n)=-m_nx\log x\le m_n/e.
$$

两项相加即为所述上界；§465 的完整预算极限 $\ell_n,m_n\to0$ 给夹逼极限。这个极限保留 $r_n$ 权重；因 $r_n\to0$，它本身不给 $D(p_n\Vert q_n)\to0$，也不给两列概率测度共同弱极限。证毕。

#### 467.4 倾斜测度先例与原算术尾的数学边界

上述通用恒等式属于经典相对熵与变换测度理论。当前钉版 Mathlib 的 [`Measure.Tilted`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Tilted.lean) 定义

$$
\frac{d(P^{\mathrm{tilt},g})}{dP}(v)
=\frac{e^{g(v)}}{\int e^g\,dP}.
$$

其 [`LogLikelihoodRatio`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean) 已有 `llr_tilted_right`、`integrable_llr_tilted_right` 和 `integral_llr_tilted_right`：在原概率测度 $P$ 下，取基测度同为 $P$，便在 $P$ 几乎处处意义下及完整积分意义下得到

$$
\log\frac{dP}{dP^{\mathrm{tilt},g}}
=-g+\log\int e^g\,dP,
\qquad
D(P\Vert P^{\mathrm{tilt},g})
=-\int g\,dP+\log\int e^g\,dP,
\tag{RSK.14}
$$

其输入是 $g$ 与 $e^g$ 的相应完整可积性。这里取实际 $P_n=p_n(v)dv$、$g(v)=\log v$：正轴上 $e^g=v$，且 $\int e^g\,dP_n=m_n/r_n$，所以其倾斜测度准确为 $Q_n=q_n(v)dv$。§465 的完整对数矩与一阶矩已给出所需纸面输入。

Mathlib 的 [`KullbackLeibler.Basic`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/InformationTheory/KullbackLeibler/Basic.lean) 使用扩展非负实数值的 `klDiv`；有限测度的公式另有总质量修正，概率测度时修正为零。RSK.6 给出实际对数似然比的完整可积性，故上述实际概率测度的相对熵有限，并且 $Q_n=P_n^{\mathrm{tilt},\log}$。

有限分类也有现成先例：[`KullbackLeibler.ChainRule`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean) 的 `klDiv_compProd_left` 给共同条件核下的相对熵不变，`klDiv_compProd_eq_add` 给完整链律。上述经典链式公式在这里的对象为 RSK.3 的原残差归一化与 RSK.8 的实际正分解；RSK.10–RSK.12 进一步把同一原 $A-L_n$ 的分类精确写成真实相邻层及实际五分类的收益。

上述概率构造依赖真实非负密度和准确正预算。算术 Möbius 原子的系数有符号，不能直接归一成这里的概率密度；改为绝对值也会改变原有符号问题。若要控制原 Robin 尾，仍需保持同一来源、同一截止及完整端点的算术运输定理。§466 的固定尺度尾合同和共同临界精度要求继续承担各自的算术义务。RSK.4–RSK.13 解释了实际解析储备怎样随递归与分类变化；原无限算术尾的最终符号仍是独立未决问题。

## 追加锚（本行以下为增补区）

## 468. 同一 Möbius 前缀的有限素数剥离群、Euler 终点与 Fibonacci 分块

沿用 §466 的标准算术 Möbius 函数及完整调和前缀

$$
H(k)=\sum_{1\le n\le k}\frac{\mu(n)}n,\qquad H(0)=0.
$$

§467 的概率归一化依赖正密度；本节保留实际有符号的 Möbius 系数，在固定整数截止的同一个有限线性空间上研究准确运输。下列证明使用经典有限 Möbius 分解、几何和及交换幺幂算子，不提出文献优先权主张。所构造的群作用于这些有限算术状态；整个 RH 判据集合的群结构不属于本节的结论。

#### 468.1 固定截止上的整数商算子

固定自然数 $N$，定义实线性空间

$$
V_N=\{f:\{0,1,\ldots,N\}\to\mathbb R:f(0)=0\}.
$$

对每个正整数 $d$，定义

$$
(T_df)(k)=f(\lfloor k/d\rfloor),\qquad 0\le k\le N.
$$

这是 $V_N$ 上的线性自映射，且 $T_1=I$。以下经典有限算子身份用于同一实际前缀的运输：对任意正整数 $d,e$，

$$
\boxed{T_dT_e=T_{de}=T_eT_d.}
\tag{FG.1}
$$

**证明。** 对每个 $0\le k\le N$，准确整数除法恒等式

$$
\left\lfloor\frac{\lfloor k/d\rfloor}{e}\right\rfloor
=\left\lfloor\frac{k}{de}\right\rfloor
$$

给逐坐标相等，包括 $k=0$。证毕。

若 $p\ge2$，则 $T_p^j=T_{p^j}$。每当 $p^K>N$，所有坐标都落在 $f(0)=0$，故 $T_p^K=0$。定义

$$
A_p=p^{-1}T_p,\qquad U_p=I-A_p,\qquad
G_{p,K}=\sum_{0\le j<K}A_p^j.
$$

对全部自然数 $K$，包括 $K=0$，有

$$
\boxed{U_pG_{p,K}=G_{p,K}U_p=I-A_p^K.}
\tag{FG.2}
$$

**证明。** 在有限和中展开 $(I-A_p)\sum_{j<K}A_p^j$，相邻幂次正负抵消，只剩 $I-A_p^K$；反向乘积相同。若 $K=0$，和为空，且 $I-A_p^0=0$。证毕。

若 $p^K>N$，FG.2 的右边为 $I$，所以

$$
\boxed{U_p^{-1}=G_{p,K}.}
\tag{FG.3}
$$

FG.1 给不同 $p$ 的 $T_p,A_p,U_p,G_{p,K}$ 全部交换。在 $V_N$ 的递增非零坐标基中，$T_p$ 严格下三角，$U_p$ 对角线恒为一，且上述有限几何和给其实际两侧逆。$N=0$ 时 $V_0$ 为零空间，这些身份仍作为零空间上的映射成立；以下范数及最小非零阶的陈述取 $N\ge1$。

#### 468.2 实际素数剥离的准确前缀运输

令 $S$ 为有限素数集合，定义 $Q_S=\prod_{q\in S}q$，空积为一，并令

$$
H_S(k)=\sum_{\substack{1\le n\le k\\(n,Q_S)=1}}\frac{\mu(n)}n,
\qquad H_S(0)=0.
$$

把这些实际函数限制到 $0,\ldots,N$，就得到同一个 $V_N$ 中的状态。$H_\varnothing=H$，且 $H_{\{2\}}$ 正是 §466 的实际奇调和前缀 $H_{\mathrm o}$。

**命题 468.1（实际素数一步与有限集合运输）。** 若 $p$ 是不属于 $S$ 的素数，则在 $V_N$ 上

$$
\boxed{H_S=U_pH_{S\cup\{p\}}.}
\tag{FG.4}
$$

对任意有限素数集合 $S$，有准确双向身份

$$
\boxed{H=\left(\prod_{p\in S}U_p\right)H_S,
\qquad H_S=\left(\prod_{p\in S}U_p^{-1}\right)H.}
\tag{FG.5}
$$

**证明。** 对每个 $k$，把与 $Q_S$ 互素的整数 $1\le n\le k$ 分为 $p$ 不整除和 $p$ 整除两部分。第一部分正是 $H_{S\cup\{p\}}(k)$。第二部分准确写成 $n=pm$，其中 $1\le m\le\lfloor k/p\rfloor$。

若 $p\mid m$，则 $p^2\mid pm$，所以 $\mu(pm)=0$。若 $p\nmid m$，标准 Möbius 函数的互素乘法性给 $\mu(pm)=-\mu(m)$。因为 $p\notin S$，有 $(pm,Q_S)=1$ 当且仅当 $(m,Q_S)=1$。因此整个第二部分准确等于

$$
-p^{-1}H_{S\cup\{p\}}(\lfloor k/p\rfloor),
$$

包括全部正端点以及 $k=0$ 的空和。这就是 FG.4。

从空集合开始，依次使用 FG.4，得到 FG.5 的第一个身份；FG.1 消去剥离顺序的影响。每个 $U_p$ 的实际两侧逆由 FG.3 给出，故再应用有限逆算子积得到第二个身份。全部整数商和几何层均保留。证毕。

#### 468.3 全部素数剥离的实际 Euler 终点

令 $P_N=\{p:p\text{ 素且 }p\le N\}$，并定义

$$
u_N(0)=0,\qquad u_N(k)=1\quad(1\le k\le N).
$$

**命题 468.2（原始前缀的有限 Euler 算子积）。** 对每个自然数 $N$，

$$
H_{P_N}=u_N,\qquad
\boxed{H=\left(\prod_{p\le N}U_p\right)u_N.}
\tag{FG.6}
$$

此外，对 $0\le k\le N$，准确有限展开为

$$
\left(\prod_{p\le N}(I-p^{-1}T_p)\right)u_N(k)
=\sum_{\substack{1\le d\le k\\d\text{ squarefree}}}
  \frac{\mu(d)}d
=H(k).
\tag{FG.7}
$$

**证明。** 对每个 $1\le k\le N$，任何 $2\le n\le k$ 都有素因子 $p\le n\le N$，所以该 $n$ 不与 $Q_{P_N}$ 互素。只有 $n=1$ 留下，其系数 $\mu(1)/1=1$。在 $k=0$ 时两边都为零。因此 $H_{P_N}=u_N$，再用 FG.5 就得 FG.6。

也可直接展开有限算子积。每个素数子集产生唯一的平方自由整数 $d$，相应算子积为 $T_d$，系数为 $\mu(d)/d$。若 $d>k$，则 $u_N(\lfloor k/d\rfloor)=u_N(0)=0$；若 $d\le k$，则该值为一。所有 $d\le k$ 的素因子都属于 $P_N$，故没有漏项。非平方自由的 $d$ 满足 $\mu(d)=0$，所以此展开正是原始完整和，得到 FG.7。

当 $N=0$ 时，$V_0$ 为零空间，产品为空积，且 $H=u_0=0$。当 $N=1$ 时，同样是空积，且 $H=u_1$。整个推导只含有限项，没有使用无穷积或无穷换序。证毕。

#### 468.4 正逆算子的准确完整范数

对 $N\ge1$，在 $V_N$ 上取最大值范数及相应算子范数。对 $p\ge2$，记

$$
K_p(N)=\min\{K\ge1:p^K>N\}.
$$

**命题 468.3（实际单素数与有限素数集合的逆预算）。** $T_p$ 的幂零阶准确为 $K_p(N)$，并且

$$
\boxed{\|U_p^{-1}\|_\infty
=\sum_{j=0}^{K_p(N)-1}p^{-j}
=\frac{1-p^{-K_p(N)}}{1-p^{-1}}
<\frac p{p-1}.}
\tag{FG.8}
$$

若 $S$ 为有限素数集合，则对全部 $f\in V_N$ 和 $0\le k\le N$，

$$
\left(\prod_{p\in S}U_p^{-1}\right)f(k)
=\sum_{\substack{1\le d\le k\\\text{every prime divisor of }d\text{ lies in }S}}
  \frac1d f(\lfloor k/d\rfloor).
\tag{FG.9}
$$

相应完整范数准确为

$$
\boxed{\left\|\prod_{p\in S}U_p^{-1}\right\|_\infty
=\sum_{\substack{1\le d\le N\\\operatorname{supp}(d)\subseteq S}}\frac1d
\le\prod_{p\in S}\frac p{p-1}.}
\tag{FG.10}
$$

其中 $\operatorname{supp}(d)$ 表示 $d$ 的素因子集合，故 $d=1$ 在每个 $S$ 的和中出现一次。

**证明。** 令 $K=K_p(N)$。由 $p^K>N$，已有 $T_p^K=0$；由最小性，$p^{K-1}\le N$。取 $f=u_N$，在 $k=p^{K-1}$ 处得到 $T_p^{K-1}f(k)=1$，所以此幂不为零，幂零阶恰为 $K$。

FG.3 中各系数 $p^{-j}$ 非负，所以逆算子的范数不超过全部有限几何权之和。在 $k=N$ 处取 $f=u_N$，其范数为一，且对每个 $j<K$，$\lfloor N/p^j\rfloor\ge1$，因而达到全部权和。这证明 FG.8 的准确等号，有限几何求和给其闭式与严格上界。

对有限 $S$，每个逆算子都是有限幂和。唯一素分解把各 $p$ 的幂次元组组合成唯一整数 $d$，权恰为 $1/d$。若 $d\le k\le N$，每个幂次自动小于 $K_p(N)$；其余元组的整数商为零，相应项为 $f(0)=0$。这给出 FG.9，没有漏掉任何可行 $d$，也没有重计系数。

FG.9 的权全部非负，故算子范数不超过 $d\le N$ 的完整权和。在 $k=N$ 处取 $f=u_N$，每个允许的 $d$ 都给 $f(\lfloor N/d\rfloor)=1$，所以此上界准确达到。与各素数的完整几何和比较便得到 FG.10。证毕。

固定有限小素数集合 $S$ 的去除因而有固定预算；若 $S=P_N$ 随截止增长，则每个 $d\le N$ 的素因子都在 $S$ 中，准确逆算子范数变为普通调和和 $\sum_{d\le N}1/d$，随 $N$ 增长。

FG.6 结合 FG.9 还给同一实际前缀的完整卷积：

$$
\boxed{\sum_{1\le d\le k}\frac1d H(\lfloor k/d\rfloor)=1
\quad(1\le k\le N).}
\tag{FG.11}
$$

**证明。** 用 $S=P_N$ 的实际逆算子积作用于 FG.6，右边恢复 $u_N$，左边由 FG.9 展开。对 $d\le k\le N$，素因子条件自动成立，且 $u_N(k)=1$，就是 FG.11。对任意整数 $k\ge1$，取 $N=k$，即得该卷积身份在所有正截止上的陈述。证毕。

#### 468.5 实际素数生成元的忠实交换群

**命题 468.4（固定截止上的自由交换群表示）。** 设 $N\ge1$。$U_p$（$p\in P_N$）生成 $GL(V_N)$ 的交换子群，并且自然群同态

$$
\mathbb Z^{P_N}\longrightarrow GL(V_N),\qquad
(m_p)_{p\in P_N}\longmapsto\prod_{p\in P_N}U_p^{m_p}
$$

是单射。因此该子群同构于自由交换群 $\mathbb Z^{\pi(N)}$。

**证明。** 各 $U_p$ 交换且可逆，故所述映射是群同态。若有非零指数，取指数非零的最小素数 $p$。较小素数的指数全为零。对 $q>p$，$T_q$ 在全部坐标 $k\le p$ 上为零，故 $U_q$ 及其有限几何逆在这些坐标上恒等，其全部整数幂同样恒等。

在同一坐标段上，$T_p^2=0$。因此对全部整数 $m$，包括正、零和负指数，有

$$
U_p^m=I-(m/p)T_p\qquad\text{在坐标 }k\le p\text{ 上}.
$$

非负指数由平方为零的二项式展开得到；负指数由此段上的 $(I-A_p)^{-1}=I+A_p$ 得到。取 $e_1(1)=1$，其余坐标为零。产品在坐标 $p$ 的值为 $-m_p/p\ne0$，而恒等作用给 $e_1(p)=0$。因此产品不是恒等，得到单射。若 $N=1$，素数集合为空，陈述是平凡群的情形。证毕。

这个群包含有符号线性状态与反向运输。FG.3 的正有限几何预算是其中具体的重构；所有群元素不能因此被视为非负预算，也没有无费用的逆操作。

#### 468.6 同一有限逆算子的 Fibonacci 分块与完整余项

**推论 468.5（准确分块与原余项运输）。** 对同一个 $A_p$，取 $G_{p,0}=0$。对全部自然数 $a,b$，

$$
\boxed{G_{p,a+b}=G_{p,a}+A_p^aG_{p,b}.}
\tag{FG.12}
$$

按标准 Fibonacci 数列 $F_0=0$、$F_1=1$、$F_{j+2}=F_{j+1}+F_j$，对全部自然数 $j$，

$$
\boxed{G_{p,F_{j+2}}
=G_{p,F_{j+1}}+A_p^{F_{j+1}}G_{p,F_j}.}
\tag{FG.13}
$$

若 $U_pf=g$，则对全部自然数 $K$ 有完整余项身份

$$
\boxed{f=G_{p,K}g+A_p^Kf.}
\tag{FG.14}
$$

**证明。** 将 $G_{p,a+b}$ 的有限和拆成前 $a$ 项及其余 $b$ 项，并从后一部分提出 $A_p^a$，即得 FG.12，包括 $a=0$ 或 $b=0$。把 $a=F_{j+1}$、$b=F_j$ 代入，得到 FG.13。

对 $N\ge1$，明确取 $K=K_p(N)$，就有 $A_p^{K_p(N)}=0$。若 $F_j\ge K_p(N)$，则 $A_p^{F_j}=0$，所以 $G_{p,F_j}=U_p^{-1}$；继续分块只是追加零层。Fibonacci 因而给同一个实际有限逆算子的准确分块顺序；任意其它自然数拆分也满足 FG.12。

若 $U_pf=g$，用 $G_{p,K}$ 作用于两边，再使用 FG.2，得到 $G_{p,K}g=(I-A_p^K)f$，移项就是 FG.14。当 $K=0$ 时，它是 $f=0+f$。证毕。

Fibonacci 分块必须运输 FG.14 的同一余项；只有达到实际幂零阶以后，才可将其置零。$p=2$、$f=H_{\mathrm o}$、$g=H$ 时，FG.14 正是 §466 的完整奇调和递归。Fibonacci 身份本身没有给出新的 Möbius 符号相消或 Robin 临界符号界。

#### 468.7 截止 5040 的估值、递归阶与分块长度

**命题 468.6（5040 的两种准确容量）。** $5040=2^4\cdot3^2\cdot5\cdot7$，因此整数本身在素数 $2,3,5,7$ 上的估值为 $(4,2,1,1)$。在整个空间 $V_{5040}$ 上，各整数商算子的幂零阶与首个覆盖该阶的 Fibonacci 长度为

| $p$ | $p^{K-1}\le5040<p^K$ | $K_p(5040)$ | 首个覆盖的 Fibonacci 长度 |
| --- | --- | ---: | ---: |
| $2$ | $4096\le5040<8192$ | $13$ | $F_7=13$ |
| $3$ | $2187\le5040<6561$ | $8$ | $F_6=8$ |
| $5$ | $3125\le5040<15625$ | $6$ | $F_6=8$ |
| $7$ | $2401\le5040<16807$ | $5$ | $F_5=5$ |

最大非零整数商幂次为 $(12,7,5,4)$。对 $S=\{2,3,5,7\}$，固定完整几何预算为

$$
\prod_{p\in S}\frac p{p-1}=\frac{35}{8},
$$

而 FG.10 的实际有限预算是完整 $S$-smooth 倒数和，严格小于 $35/8$。

**证明。** 上述因子分解直接给四个素数估值。各行的相邻素数幂分别为 $2^{12}=4096$、$2^{13}=8192$，$3^7=2187$、$3^8=6561$，$5^5=3125$、$5^6=15625$，以及 $7^4=2401$、$7^5=16807$。由 $K_p$ 的定义得到四个幂零阶，并由 $F_5=5$、$F_6=8$、$F_7=13$ 得表中的首个覆盖长度。最大非零幂次是各 $K_p-1$。

乘四个几何上界得到

$$
2\cdot\frac32\cdot\frac54\cdot\frac76=\frac{35}{8}.
$$

实际有限和由 FG.10 给出；完整几何积还包含超过截止的正权项，故该有限和严格小于 $35/8$。证毕。

整数本身的估值容量与整个区间的递归容量因而分别为 $(4,2,1,1)$ 与 $(12,7,5,4)$。同一有限算子构造适用于其它截止 $N$；上述表并未解释 $5040$ 在 Robin 判据中的极端性，也未给拓扑上的 Klein 瓶染色例外与 FG.1–FG.14 的数学映射。

#### 468.8 完整算术衰减与原临界尾的边界

FG.5 与 FG.8–FG.10 准确运输固定有限素数剥离的预算。它们保留标准 Möbius 系数、同一整数截止及全部端点；§466 的 $p=2$ 身份是其中实际的一步及完整递归。任意素数集合的这类有限运输不自动给出随截止增长的统一逆预算，正如 $S=P_N$ 时的准确范数为增长的普通调和和。

对同一完整 $H$ 的 Gaussian 型定量衰减仍是另一项算术义务。同时增长的素数集合 $S$、Robin 增长权、共同临界尺度以及原有符号尾的符号也各须控制。有限交换群与 Fibonacci 分块没有自行履行这些义务；原 RH 目标仍需相应的准确估计。

## 追加锚（本行以下为增补区）

## 469. 实际素数运输的幂次衰减类、完整逆成本与同一 H 的商区间变差

保持 §468 的同一空间 $V_N$、整数商算子 $T_d$、$A_p=p^{-1}T_p$、$U_p=I-A_p$，以及标准 Möbius 调和前缀 $H,H_S$。任意向量只用于计算算子范数；前缀运输仍消费 FG.4–FG.5 的实际算术身份。本节使用经典加权最大范数、有限几何和及矩阵行范数，给出这些实际有限算子的准确成本，不提出文献优先权主张。

#### 469.1 加权范数与完整整数商估计

固定 $0\le\alpha<1$ 和自然数 $N$，在 $V_N$ 上定义

$$
\|f\|_{\alpha,N}
=\max\left(\{0\}\cup
 \{(k+1)^\alpha|f(k)|:1\le k\le N\}\right).
$$

对 $N\ge1$，各权严格正，此式是范数；齐次性与三角不等式由各坐标的绝对值及有限最大值给出。对 $N=0$，$V_0$ 为零空间，此式给其唯一向量范数零。用同一记号表示诱导算子范数；零空间上包括恒等及逆映射在内的全部算子范数均为零。以下非空行最大值公式取 $N\ge1$。

对每个正整数 $d$ 和 $k\ge0$，写 $k=dq+r$，其中 $0\le r<d$。准确整数商给

$$
k+1=dq+r+1\le d(q+1),\qquad
\lfloor k/d\rfloor+1\ge(k+1)/d.
\tag{WN.1}
$$

若 $q=0$，则 $T_df(k)=f(0)=0$。若 $q\ge1$，则

$$
(k+1)^\alpha|T_df(k)|
\le\left(\frac{k+1}{q+1}\right)^\alpha\|f\|_{\alpha,N}
\le d^\alpha\|f\|_{\alpha,N}.
$$

因此 $\|T_d\|_{\alpha,N}\le d^\alpha$，包括 $\alpha=0$。这一估计保留准确 floor 和零坐标。

#### 469.2 整数商算子的准确分段范数

**命题 469.1（同一实际 $T_d$ 的完整范数）。** 对 $N\ge1$ 及正整数 $d$，

$$
\|T_d\|_{\alpha,N}
=\begin{cases}
0,&N<d,\\
\displaystyle\max_{d\le k\le N}
 \left(\frac{k+1}{\lfloor k/d\rfloor+1}\right)^\alpha,&N\ge d,
\end{cases}
\tag{WN.2}
$$

并有准确闭式

$$
\boxed{
\|T_d\|_{\alpha,N}
=\begin{cases}
0,&N<d,\\
((N+1)/2)^\alpha,&d\le N<2d-1,\\
d^\alpha,&N\ge2d-1.
\end{cases}}
\tag{WN.3}
$$

所以对 $p\ge2$，

$$
\|A_p\|_{\alpha,N}=p^{-1}\|T_p\|_{\alpha,N}
\le p^{\alpha-1}<1.
\tag{WN.4}
$$

**证明。** 若 $N<d$，所有商为零，算子为零。其余情形的上界由 WN.1 的坐标估计给出。对任一最大行 $k$，令 $q=\lfloor k/d\rfloor\ge1$，取仅在 $q$ 非零的向量 $f(q)=(q+1)^{-\alpha}$。其范数为一，且输出在 $k$ 处达到该行权比，证明 WN.2 的准确等号。

当 $d\le N<2d-1$ 时，唯一非零商为一，最大权比在 $k=N$ 处为 $(N+1)/2$。当 $N\ge2d-1$ 时，取 $k=2d-1$，商为一且权比为 $d$，达到 WN.1 的上界。这给 WN.3。$d=1$ 时中间区间为空，且 $T_1=I$。$\alpha=0$ 时每个非零情形的范数均为一，零算子的情形仍为零。

标量乘法给 $\|A_p\|=p^{-1}\|T_p\|$。因为 $p>1$ 且 $\alpha-1<0$，有 $p^{\alpha-1}<1$，得到 WN.4。若 $p>N$，则 $A_p=0$。证毕。

#### 469.3 一个素数的正向成本与完整正逆成本

**命题 469.2（实际 $U_p$ 及其逆的准确加权范数）。** 对 $N\ge1$、$p\ge2$，

$$
\boxed{\|U_p\|_{\alpha,N}
=1+p^{-1}\|T_p\|_{\alpha,N}
\le1+p^{\alpha-1}.}
\tag{WN.5}
$$

取 $K=K_p(N)$、$q=p^{\alpha-1}$，则

$$
\boxed{\|U_p^{-1}\|_{\alpha,N}
=\max_{1\le k\le N}
 \sum_{\substack{0\le j<K\\p^j\le k}}
 p^{-j}
 \left(\frac{k+1}{\lfloor k/p^j\rfloor+1}\right)^\alpha.}
\tag{WN.6}
$$

相应有限几何上界为

$$
\boxed{\|U_p^{-1}\|_{\alpha,N}
\le\sum_{j=0}^{K-1}q^j
=\frac{1-q^K}{1-q}
<\frac1{1-p^{\alpha-1}}.}
\tag{WN.7}
$$

在 $0<\alpha<1$ 时，WN.7 的有限几何上界准确达到，当且仅当

$$
N\ge2p^{K-1}-1.
\tag{WN.8}
$$

**证明。** $k\ge p$ 的行有两个不同的非零坐标 $k$ 和 $\lfloor k/p\rfloor$，系数分别为 $1$ 和 $-1/p$。其加权绝对行和等于一加该整数商行的权比除以 $p$。取这两个输入坐标具有相反符号及相应逆权，就达到该行和。$k<p$ 的行仅有对角系数一，所以 WN.2 给 WN.5，包括 $p>N$ 时范数为一。

FG.3 的逆算子系数全为正，每个范数不超过一的向量给 WN.6 中相应的行和上界。取

$$
f_\alpha(0)=0,\qquad
f_\alpha(k)=(k+1)^{-\alpha}\quad(1\le k\le N),
$$

其加权范数为一，且同时达到每个正系数行和。因此 WN.6 给准确范数。这里 $f_\alpha$ 是范数见证，不替代原实际 Möbius 前缀。

对每个 $d=p^j$ 应用 WN.1，得到行和各项不超过 $q^j$，有限求和就是 WN.7。$\alpha=0$ 时各非零权比均为一，最大行 $k=N$ 包含全部 $j<K$，准确恢复 FG.8。

若 $\alpha>0$，达到全部 $K$ 项的几何上界需要 $k\ge p^{K-1}$，且最高幂次的 floor 权比达到 $p^{K-1}$。后者等价于 $k+1$ 可被 $p^{K-1}$ 整除；使该商非零的最小这样的 $k$ 是 $2p^{K-1}-1$。此坐标还同时达到所有低幂次的权比。若它超过 $N$，少于 $K$ 项的行缺少正项，而含全部 $K$ 项的行在最高幂次处有严格权比损失，有限最大值就严格小于几何上界。这证明 WN.8。$K=1$ 时阈值为一。

当 $N=1$ 时，每个 $p\ge2$ 都给 $T_p=0$、$U_p=U_p^{-1}=I$，加权范数为一。$N=0$ 时这些映射在零空间的算子范数为零；统一上界仍有效，非空行最大值公式则取 $N\ge1$。证毕。

#### 469.4 完整有限余项及其收缩预算

**命题 469.3（同一原余项的加权运输）。** 对全部自然数 $K$，若 $f,g\in V_N$ 且 $U_pf=g$，则保持 FG.14 的完整身份

$$
f=G_{p,K}g+A_p^Kf,
$$

并且

$$
\boxed{\|f-G_{p,K}g\|_{\alpha,N}
\le p^{(\alpha-1)K}\|f\|_{\alpha,N}.}
\tag{WN.9}
$$

对 $N\ge1$，余项算子准确范数为 $p^{-K}\|T_{p^K}\|_{\alpha,N}$，其中 $\|T_{p^K}\|$ 由 WN.2–WN.3 给出；当 $p^K>N$ 时，余项准确为零。

**证明。** FG.2 给 $G_{p,K}g=(I-A_p^K)f$，移项即为原完整身份。又 $A_p^K=p^{-K}T_{p^K}$，应用 WN.1 及标量范数齐次性得到 WN.9 和准确余项范数。$K=0$ 时 $G_{p,0}=0$，身份为 $f=0+f$，估计为 $\|f\|\le\|f\|$。在零空间上两边均为零。证毕。

部分几何和的准确范数也由 WN.6 的正行和论证给出：把范围 $j<K_p(N)$ 改为 $j<K$ 即可，其上界是对应的有限 $q^j$ 和。超过实际幂零阶的项准确为零。因此 FG.12–FG.13 的 Fibonacci 分块可以同时运输这一收缩估计与同一有限余项；达到真实截止阈值以后才可删去余项。

对实际素数一步，取 $p\notin S$、$f=H_{S\cup\{p\}}$、$g=H_S$，就是 FG.4 的原算术状态。幂零以前，WN.9 消费的是 $f$ 的实际有限范数，没有据此设定它的统一衰减。幂零以后，余项消失，完整逆运输由 $g$ 的预算独立控制。

#### 469.5 固定素数集合保持同一幂次衰减类

对固定有限素数集合 $S$，定义

$$
B_\alpha(S)=\prod_{p\in S}(1-p^{\alpha-1})^{-1},\qquad
C_\alpha(S)=\prod_{p\in S}(1+p^{\alpha-1}).
$$

二者均有限，空积为一，且不依赖截止 $N$。

**命题 469.4（实际前缀的双向幂次运输）。** 对全部自然数 $N$，

$$
\boxed{
\|H_S\|_{\alpha,N}\le B_\alpha(S)\|H\|_{\alpha,N},\qquad
\|H\|_{\alpha,N}\le C_\alpha(S)\|H_S\|_{\alpha,N}.}
\tag{WN.10}
$$

因此，对每个固定 $S$，两个实际前缀的给定衰减类满足

$$
H(k)=O((k+1)^{-\alpha})
\quad\Longleftrightarrow\quad
H_S(k)=O((k+1)^{-\alpha}).
$$

**证明。** 对 FG.5 的同一双向身份应用算子范数的次乘性，再分别使用 WN.5 与 WN.7，就得 WN.10。若 $|H(k)|\le C(k+1)^{-\alpha}$ 对所有 $k\ge1$ 成立，则各截止的 $\|H\|_{\alpha,N}\le C$；对每个 $k$ 取 $N=k$，WN.10 给

$$
|H_S(k)|\le B_\alpha(S)C(k+1)^{-\alpha}.
$$

反向同理，常数为 $C_\alpha(S)C$。这证明两方向的衰减类身份，包括 $\alpha=0$、$\alpha=1/2$。$N=0$ 时两边范数均为零；$N=1$ 时各前缀唯一正坐标都等于一，逆与正向算子均为恒等。空集合 $S$ 给两个预算一及 $H_S=H$。证毕。

$\alpha=1/2$ 表示这项条件运输的平方根幂次尺度。这里没有证明实际 $H$ 或 $H_S$ 具有该衰减，也没有给出此端点与 RH 的等价定理；原 Robin 有符号尾的符号仍须另证。

#### 469.6 完整正逆行范数与随截止增长的成本

**命题 469.5（实际有限素数逆成本及全素数增长）。** 对 $N\ge1$ 和有限素数集合 $S$，

$$
\boxed{
\left\|\prod_{p\in S}U_p^{-1}\right\|_{\alpha,N}
=\max_{1\le k\le N}
 \sum_{\substack{1\le d\le k\\\operatorname{supp}(d)\subseteq S}}
 \frac1d
 \left(\frac{k+1}{\lfloor k/d\rfloor+1}\right)^\alpha.}
\tag{WN.11}
$$

此准确范数不超过

$$
\sum_{\substack{1\le d\le N\\\operatorname{supp}(d)\subseteq S}}
 d^{\alpha-1}
\le B_\alpha(S).
\tag{WN.12}
$$

若 $S=P_N$ 且 $0<\alpha<1$，则

$$
\boxed{
\frac{(N+1)^\alpha}{2^{\alpha+1}}
\le\left\|\prod_{p\le N}U_p^{-1}\right\|_{\alpha,N}
\le\sum_{d=1}^{N}d^{\alpha-1}
\le1+\frac{N^\alpha-1}{\alpha}.}
\tag{WN.13}
$$

所以对每个固定 $0<\alpha<1$，全素数逆范数为 $\Theta(N^\alpha)$，在 $\alpha=1/2$ 时为 $\Theta(\sqrt N)$。$\alpha=0$ 时，它准确等于普通调和和 $\sum_{d=1}^N1/d$。

**证明。** FG.9 给完整正系数逆展开。每个范数不超过一的向量给 WN.11 的行和上界；同一 $f_\alpha(k)=(k+1)^{-\alpha}$ 同时达到各行，因而最大行和就是准确算子范数。WN.1 把每个权比控制为 $d^\alpha$，给 WN.12 的第一个上界。对各素数的非负几何和求有限积，完整 $S$-smooth 和不超过 $B_\alpha(S)$，得到第二个上界。

当 $\alpha=0$ 时，各非零权比等于一，行和随 $k$ 增加，最大值在 $N$，准确恢复 FG.10。当 $S=P_N$ 时，所有 $d\le k$ 的素因子条件自动成立，因此此范数为普通调和和。其增长也由初等积分比较给出。

对 $\alpha>0$ 的全素数下界，取 WN.11 的行 $k=N$，仅保留 $d>\lfloor N/2\rfloor$。每个这样的 $d$ 都有 $\lfloor N/d\rfloor=1$，共有 $\lceil N/2\rceil$ 项，每项倒数至少为 $1/N$，所以其倒数和至少为 $1/2$。该行贡献因而至少为 $(N+1)^\alpha/2^{\alpha+1}$。

上界由 WN.12 保留全部整数 $d\le N$ 给出。因为 $x^{\alpha-1}$ 递减，

$$
\sum_{d=1}^N d^{\alpha-1}
\le1+\int_1^N x^{\alpha-1}\,dx
=1+\frac{N^\alpha-1}{\alpha}.
$$

这证明 WN.13 及所述阶数，包括 $N=1$ 的上界等号；不需要任何素数分布渐近。证毕。

正 $\alpha$ 时，准确逆范数是完整行最大值。floor 权比会跳变，不能把 WN.11 的最大值未经证明地替换为 $k=N$。零空间 $N=0$ 的算子范数仍为零；$N=1$ 的实际逆为恒等，范数为一。

固定 $S$ 的 WN.10 因而不能直接作为增长集合 $S_N$ 的统一预算。全素数情形给出明确的逆成本增长；同时增长的素数集合、实际衰减率与原截止需要联合估计，有限可逆身份本身保持成立。

#### 469.7 同列有符号系数与原 H 的完整商区间变差

**命题 469.6（实际正向成本的商区间身份）。** 取 $N\ge1$ 和有限素数集合 $S$。定义

$$
c_{k,j}(S)=
\sum_{\substack{1\le d\le k\\d\text{ squarefree}\\
 \operatorname{supp}(d)\subseteq S\\\lfloor k/d\rfloor=j}}
 \frac{\mu(d)}d,
\qquad 1\le j\le k\le N.
$$

则实际正向算子范数准确为

$$
\left\|\prod_{p\in S}U_p\right\|_{\alpha,N}
=\max_{1\le k\le N}(k+1)^\alpha
 \sum_{j=1}^{k}\frac{|c_{k,j}(S)|}{(j+1)^\alpha}.
\tag{WN.14}
$$

在 $S=P_N$ 时，全部完整系数来自同一原始前缀：

$$
\boxed{c_{k,j}(P_N)
=H(\lfloor k/j\rfloor)-H(\lfloor k/(j+1)\rfloor).}
\tag{WN.15}
$$

因此完整正向成本正是

$$
\boxed{
\left\|\prod_{p\le N}U_p\right\|_{\alpha,N}
=\max_{1\le k\le N}(k+1)^\alpha
\sum_{j=1}^{k}
\frac{|H(\lfloor k/j\rfloor)-H(\lfloor k/(j+1)\rfloor)|}
 {(j+1)^\alpha}.}
\tag{WN.16}
$$

**证明。** 展开有限 $U_p$ 积，每个素数子集产生平方自由 $d$，系数为标准 $\mu(d)/d$。若 $d>k$，输出为 $f(0)=0$；其余项按相同输出坐标 $j=\lfloor k/d\rfloor$ 合并，便得到系数 $c_{k,j}(S)$。因此每行输出是 $\sum_{j=1}^k c_{k,j}(S)f(j)$，加权绝对行和给 WN.14 的上界。取最大行，令输入坐标具有该行系数的符号与对应逆权 $(j+1)^{-\alpha}$，其范数为一并达到该行和，证明准确等号。每行对角系数 $c_{k,k}=1$，所以范数见证不是零向量。

若 $S=P_N$，每个 $d\le k\le N$ 的素因子都属于 $S$，且非平方自由项的 Möbius 系数为零。准确整数商条件为

$$
\lfloor k/d\rfloor=j
\quad\Longleftrightarrow\quad
\lfloor k/(j+1)\rfloor<d\le\lfloor k/j\rfloor.
$$

把这段原始有限和写成两个完整前缀之差，就得到 WN.15，两个端点均保留。$j=k$ 时，它给 $H(1)-H(0)=1$；若两个整数商相同，区间为空，系数准确为零。将 WN.15 代入 WN.14 就是 WN.16。证毕。

WN.14 的绝对值作用于同列的有符号系数合并以后；WN.11 的逆系数则全部为正。这将正向成本落实为同一实际 $H$ 的完整有限加权商区间变差，没有把 Möbius 系数改成无符号模型。$\alpha=0$ 时这些式子同样成立；$N=1$ 时唯一行系数为一；$N=0$ 时无正坐标，原零空间算子范数为零。

#### 469.8 衰减输入、完整变差估计与原有符号尾的义务

固定有限素数剥离可以保持已经给定的幂次衰减类。剥离全部素数时，平方根加权逆成本却随截止按 $\sqrt N$ 增长。WN.16 给正向成本的同源完整变差身份，但尚无使该变差足够小的估计；恒等式没有自行建立原实际 $H$ 的衰减。

原 Robin 有符号尾仍有自己的增长权、截止、完整端点及共同临界尺度义务。要把这里的变差成本用于该尾，仍须准确控制同一来源、同一尺度的运输；有限绝对范数也不提供所需算术符号。对实际商区间系数的定量估计和增长集合 $S_N$ 的联合预算是尚未完成的数学问题，RH 及原尾的最终符号继续开放。

## 追加锚（本行以下为增补区）

## 470. 单点商块与增长素数剥离的统一算子预算障碍

保持 §468–§469 的实际空间 $V_N$、$T_d$、$U_p$、$P_N$ 与标准 Möbius 调和前缀 $H$。本节给出 WN.16 中完整正向成本的下界，确定随截止增长的全素数剥离不能在任意输入的加权最大范数上拥有统一预算。所用素数倒数发散是经典定理，见 Aigner–Ziegler《Proofs from THE BOOK》第一章的 Erdős 证明；有限最大范数及商块恒等式沿用 §469。本节不提出这些经典结果的数学优先权主张。

#### 470.1 同一实际前缀的行预算

对自然数 $k$ 与正整数 $j$，定义

$$
c_{k,j}=H(\lfloor k/j\rfloor)-H(\lfloor k/(j+1)\rfloor),
\qquad
V_k(w)=\sum_{j=1}^{k}|c_{k,j}|w(j).
\tag{QO.1}
$$

由 WN.15，$c_{k,j}$ 正是所有 $1\le d\le k$ 且 $\lfloor k/d\rfloor=j$ 的实际有符号系数 $\mu(d)/d$ 之和。正整数商的完整区间为 $(\lfloor k/(j+1)\rfloor,\lfloor k/j\rfloor]$。商零的实际纤维为空；QO.1 的前缀差公式只对正 $j$ 使用。

对 $\alpha\ge0$，定义完整加权行成本

$$
w_{k,\alpha}(j)=\left(\frac{k+1}{j+1}\right)^\alpha,
\qquad
R_\alpha(k)=V_k(w_{k,\alpha}).
\tag{QO.2}
$$

$k=0$ 时这些行和均为空，值为零；$k\ge1$ 时 WN.16 给

$$
\left\|\prod_{p\le N}U_p\right\|_{\alpha,N}
=\max_{1\le k\le N}R_\alpha(k)
\qquad(N\ge1).
\tag{QO.3}
$$

当 $\alpha\ge1$ 时，仍用 §469.1 的显示公式定义有限加权最大范数。QO.3 的正权有限行最大值证明不使用 $\alpha<1$，因此也适用于这一范围。

这里单位输入盒为 $|f(j)|\le(j+1)^{-\alpha}$；$R_\alpha(k)$ 包括输出坐标的因子 $(k+1)^\alpha$。对每个固定行，其系数符号的有限选择达到该行成本。达到某一行的输入可以依赖该行，QO.3 不要求一个输入同时达到全部行。

#### 470.2 小分母的实际商纤维为单点

**命题 470.1（完整单点商块）。** 设 $L\ge1$、$k\ge L(L+1)$ 为整数。对每个 $1\le d\le L$，写 $q_d=\lfloor k/d\rfloor$，则 $1\le q_d\le k$，并且

$$
\{e:1\le e\le k,\ \lfloor k/e\rfloor=q_d\}=\{d\}.
\tag{QO.4}
$$

这些 $q_d$ 互不相同，实际商块系数满足

$$
c_{k,q_d}=\frac{\mu(d)}d.
\tag{QO.5}
$$

**证明。** 因为 $k\ge L(L+1)\ge d(d+1)$，

$$
\frac{k}{d}-\frac{k}{d+1}=\frac{k}{d(d+1)}\ge1.
$$

对实数 $x\ge y+1$ 有 $\lfloor x\rfloor\ge\lfloor y\rfloor+1$，因此

$$
\lfloor k/d\rfloor>\lfloor k/(d+1)\rfloor.
\tag{QO.6}
$$

若 $d>1$，同理由 $k\ge d(d-1)$ 得

$$
\lfloor k/(d-1)\rfloor>\lfloor k/d\rfloor.
\tag{QO.7}
$$

函数 $e\mapsto\lfloor k/e\rfloor$ 在正整数上递减。任何 $e>d$ 的商不超过 QO.6 的右项，任何 $e<d$ 的商在 $d>1$ 时不小于 QO.7 的左项，因而都不能等于 $q_d$。当 $d=1$ 时不存在正整数 $e<d$。分母 $d$ 本身满足原窗口条件，故纤维准确为 $\{d\}$。

$1\le d\le k$ 给 $q_d\ge1$，且 $q_d\le k$。若两个小分母给同一个商，QO.4 强制它们相等，所以这些商互异。对原有符号纤维求和即得 QO.5；其中没有其它分母的项可以抵消。证毕。

#### 470.3 完整有限下界与加权预算发散

**命题 470.2（同一行预算的准确来源下界）。** 对命题 470.1 的 $L,k$ 和每个 $\alpha\ge0$，

$$
\boxed{
R_\alpha(k)\ge
2^{-\alpha}\sum_{d=1}^{L}|\mu(d)|d^{\alpha-1}
\ge2^{-\alpha}\sum_{\substack{p\le L\\p\ \mathrm{prime}}}
p^{\alpha-1}.}
\tag{QO.8}
$$

完整有限上界仍为

$$
R_\alpha(k)\le\sum_{d=1}^{k}|\mu(d)|d^{\alpha-1}
\le\sum_{d=1}^{k}d^{\alpha-1}.
\tag{QO.9}
$$

对每个固定 $\alpha\ge0$，$R_\alpha(k)\to+\infty$，特别是普通行预算 $V_k(1)=R_0(k)$ 不统一有界。于是

$$
\boxed{
\left\|\prod_{p\le N}U_p\right\|_{\alpha,N}
\longrightarrow+\infty\quad(N\to\infty).}
\tag{QO.10}
$$

**证明。** QO.4–QO.5 给互异的单点坐标，故在完整非负行和中只保留这些坐标，得到

$$
R_\alpha(k)\ge\sum_{d=1}^{L}\frac{|\mu(d)|}{d}
\left(\frac{k+1}{q_d+1}\right)^\alpha.
$$

准确整数商给 $dq_d\le k$，而 $d\le k$，所以

$$
d(q_d+1)\le k+d\le2(k+1),\qquad
\frac{k+1}{q_d+1}\ge\frac d2.
$$

因为 $\alpha\ge0$，提升到该幂次保持不等号，便得 QO.8 的第一个下界。素数 $p$ 满足 $\mu(p)=-1$，只保留素数项给第二个下界。$\alpha=0$ 时因子 $2^{-\alpha}$ 为一，直接得到

$$
V_k(1)\ge\sum_{d=1}^{L}\frac{|\mu(d)|}d
\ge\sum_{\substack{p\le L\\p\ \mathrm{prime}}}\frac1p.
\tag{QO.11}
$$

为证 QO.9，在每个完整纤维内使用三角不等式，随后对原全部分母求和。WN.1 给 $(k+1)/(\lfloor k/d\rfloor+1)\le d$，因此

$$
R_\alpha(k)\le\sum_{d=1}^{k}\frac{|\mu(d)|}d
\left(\frac{k+1}{\lfloor k/d\rfloor+1}\right)^\alpha
\le\sum_{d=1}^{k}|\mu(d)|d^{\alpha-1}.
$$

$|\mu(d)|\le1$ 给剩余上界，未移除任何实际有限项。

对每个素数 $p$，$p^\alpha\ge1$，故 $p^{\alpha-1}\ge1/p$。经典素数倒数发散定理说明 QO.8 的素数部分和随 $L$ 趋于正无穷。对任给实数 $B$，选 $L\ge1$ 使该下界大于 $B$；然后每个 $k\ge L(L+1)$ 都满足 $R_\alpha(k)>B$。这证明整条序列趋于正无穷，而不只是某个子列无界。

最后，对任意 $N\ge1$，QO.3 的完整行最大值至少为 $R_\alpha(N)$。因此行成本的发散推出 QO.10。此处只是用末行提供下界，没有把准确最大值替换为末行。证毕。

#### 470.4 平方自由计数给出完整量化增长

写 $a_d=|\mu(d)|$，并定义

$$
Q(L)=\sum_{d=1}^{L}a_d,\qquad
\mathcal H_L=\sum_{d=1}^{L}\frac1d,
$$

两者在 $L=0$ 时均为零。对正 $d$，$a_d$ 是平方自由整数的指示系数。

**命题 470.3（实际有符号算子的量化成本）。** 对每个自然数 $L$，

$$
Q(L)\ge\frac L4,\qquad
\sum_{d=1}^{L}\frac{|\mu(d)|}d\ge\frac14\mathcal H_L.
\tag{QO.14}
$$

因此，当 $L\ge1$、$k\ge L(L+1)$ 时，

$$
R_0(k)\ge\frac14\mathcal H_L,\qquad
R_\alpha(k)\ge2^{-\alpha-2}L^\alpha\quad(0<\alpha<1).
\tag{QO.15}
$$

记 $F_{\alpha,N}=\|\prod_{p\le N}U_p\|_{\alpha,N}$。对每个 $N\ge16$，有完整界

$$
\boxed{\frac1{16}\log N\le F_{0,N}\le\mathcal H_N\le1+\log N,}
\tag{QO.16}
$$

以及

$$
\boxed{
2^{-2\alpha-2}N^{\alpha/2}\le F_{\alpha,N}
\le1+\frac{N^\alpha-1}{\alpha}
\quad(0<\alpha<1).}
\tag{QO.17}
$$

特别地，普通正向范数为 $\Theta(\log N)$；对 $\alpha=1/2$，正向范数至少为 $N^{1/4}/8$。QO.17 没有断言正 $\alpha$ 的准确增长阶等于 $N^{\alpha/2}$。

**证明。** 每个正的非平方自由整数 $d\le L$ 都有某个整数 $n\ge2$ 满足 $n^2\mid d$，且 $n\le d\le L$。因此全部非平方自由整数被有限集合

$$
B_n(L)=\{d:1\le d\le L,\ n^2\mid d\},\qquad2\le n\le L,
$$

覆盖。每个 $B_n(L)$ 的基数准确为 $\lfloor L/n^2\rfloor$，由 $m\mapsto mn^2$ 与 $1\le m\le\lfloor L/n^2\rfloor$ 的双射给出。当 $n^2>L$ 时，该集合及其计数均为零。有限并集的基数不超过各基数之和，故

$$
L-Q(L)\le\sum_{n=2}^{L}\lfloor L/n^2\rfloor
\le L\sum_{n=2}^{L}\frac1{n^2}\le\frac{3L}4.
$$

最后一步在 $L\ge2$ 时由完整有限望远镜和给出：

$$
\sum_{n=2}^{L}\frac1{n^2}
\le\frac14+\sum_{n=3}^{L}\frac1{n(n-1)}
=\frac34-\frac1L\le\frac34.
$$

$L=2$ 时中间和为空，等式右端为 $1/4$。$L=0,1$ 的非平方自由集合为空，且 $Q(0)=0$、$Q(1)=1$，直接满足计数界。这证明 QO.14 的第一式，未用无穷并集，也未把实数界替换为未证明的整数取整界。

对 $L\ge1$，完整有限 Abel 恒等式保留终端项：

$$
\sum_{d=1}^{L}\frac{a_d}d
=\frac{Q(L)}L+
\sum_{m=1}^{L-1}Q(m)\left(\frac1m-\frac1{m+1}\right).
$$

括号内系数非负，把每个 $Q(m)$ 的计数界及终端 $Q(L)\ge L/4$ 代入，得到

$$
\sum_{d=1}^{L}\frac{a_d}d
\ge\frac14+\frac14\sum_{m=1}^{L-1}\frac1{m+1}
=\frac14\mathcal H_L.
$$

$L=1$ 时内部和为空；$L=0$ 时原两边均为零，独立成立。对 $0<\alpha<1$ 和 $L\ge1$，因为 $d^{\alpha-1}\ge L^{\alpha-1}$ 对 $1\le d\le L$ 成立，

$$
\sum_{d=1}^{L}a_dd^{\alpha-1}
\ge L^{\alpha-1}Q(L)\ge\frac14L^\alpha.
$$

将这两个界代入 QO.8 或 QO.11，得到 QO.15。

现在取 $N\ge16$，令 $s=\lfloor\sqrt N\rfloor$、$L=s-1$。因为 $\sqrt N\ge4$，有 $L\ge\sqrt N-2\ge\sqrt N/2\ge1$，并且 $L(L+1)=s(s-1)\le s^2\le N$。QO.3 与 QO.15 给

$$
F_{\alpha,N}\ge R_\alpha(N)
\ge2^{-\alpha-2}L^\alpha
\ge2^{-2\alpha-2}N^{\alpha/2}
\quad(0<\alpha<1).
$$

普通调和和的积分比较给 $\mathcal H_L\ge\log(L+1)$ 和 $\mathcal H_N\le1+\log N$。又 $L+1=s\ge\sqrt N/2$，所以

$$
F_{0,N}\ge\frac14\log(L+1)
\ge\frac18\log N-\frac14\log2
\ge\frac1{16}\log N,
$$

最后一步使用 $\log N\ge\log16=4\log2$。完整 QO.9 对每个 $k\le N$ 给 $R_0(k)\le\mathcal H_k\le\mathcal H_N$，得到 QO.16 的上界。对正 $\alpha<1$，同样对全部行使用 QO.9，然后用递减函数 $x^{\alpha-1}$ 的积分比较，得到

$$
F_{\alpha,N}\le\sum_{d=1}^{N}d^{\alpha-1}
\le1+\int_1^N x^{\alpha-1}\,dx
=1+\frac{N^\alpha-1}{\alpha}.
$$

这证明 QO.17。$\alpha=1/2$ 时下界系数为 $2^{-3}=1/8$。证毕。

#### 470.5 任意输入盒、固定剥离及实际算术状态的不同量词

**推论 470.4（统一任意输入预算的障碍）。** 对每个固定 $\alpha\ge0$， 不存在不依赖 $N$ 的实数 $C$，使每个 $N\ge1$ 和每个 $f\in V_N$ 都满足

$$
\left\|\left(\prod_{p\le N}U_p\right)f\right\|_{\alpha,N}
\le C\|f\|_{\alpha,N}.
\tag{QO.12}
$$

**证明。** 如果这样的 $C$ 存在，取单位输入的上确界，全部诱导范数不超过 $C$，与 QO.10 矛盾。等价地，在 QO.3 的最大行按合并系数选择有限输入符号，即得违反任何给定统一 $C$ 的向量。证毕。

对 $0\le\alpha<1$ 及固定有限素数集合 $S$，WN.10 的双向运输常数 $B_\alpha(S)$、$C_\alpha(S)$ 仍然有限且不依赖 $N$，给定幂次衰减类的等价性保持成立。QO.10 使用的是随 $N$ 增长的 $P_N$，因此没有否定固定集合的运输结论。

实际算术输入也可以与最大范数见证具有不同的符号结构。令 $\mathbf1_+(0)=0$、$\mathbf1_+(j)=1$ 对所有正 $j$，则同一实际算子满足

$$
\left(\prod_{p\le N}U_p\right)\mathbf1_+(k)
=\sum_{d=1}^{k}\frac{\mu(d)}d=H(k),\qquad1\le k\le N.
\tag{QO.13}
$$

经典 Möbius floor 恒等式 $\sum_{d=1}^{k}\mu(d)\lfloor k/d\rfloor=1$ 保留完整小数余项，给

$$
kH(k)=1+\sum_{d=1}^{k}\mu(d)\{k/d\},\qquad
|H(k)|\le1+1/k\le2\quad(k\ge1).
$$

因此在普通最大范数中，这个特定输入的输出统一有界，而 QO.10 的算子范数仍然发散。对于实际 $H$ 的更强衰减或原 Robin 权族，需要直接控制它们的相关符号与完整端点；任意输入盒的绝对范数会允许独立选择符号，不能代替这些算术条件。

QO.8–QO.12 排除的是增长全素数剥离在任意输入盒上的统一算子预算。它们没有排除附带实际输入结构的变差估计、随截止增长的定量预算或原 Robin 有符号尾的其它估计。RH 以及该原尾的最终符号仍未由这些有限算子结论确定。

## 追加锚（本行以下为增补区）

### 471. 实际阶乘余项的固定域求导与完整尾的较低衰减门槛

本节保持原阶乘余项、原 Robin 权及全部无限积分，证明一条固定 $x$ 的充分尾条件。阶乘跳跃留在积分变量中，尺度导数落在光滑权上；这允许直接支付完整导数，而不对一个误差上界求导。所有对数均为自然对数。

#### 471.1 实际对象与完整低高分解

对 $y>0$ 定义

$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
\qquad w(t)=\frac{1+\log t}{t^2\log^2t}.
$$

对 $x\ge e$、$s\ge x$ 保持

$$
P_x(s)=\int_x^\infty\eta(t/s)w(t)\,dt,
\quad Q_x(s)=sP_x(s),
\quad b_x(s)=s[P_x(s)-P_x(2s)].
\tag{FD.1}
$$

有限恒等式 $\sum_{n=1}^{N}\log n=\log(N!)$ 将 $\eta$ 识别为实际对数前缀的余项。经典有限阶乘误差给出

$$
\eta(y)=y(1-\log y)\quad(0<y\le1),
\qquad |\eta(y)|\le1+\log y\quad(y\ge1).
\tag{FD.2}
$$

第一式包含 $y=1$，因为 $0!=1!=1$。第二式使用完整有限阶乘误差，不要求 $y$ 是整数。本节直接采用已有有限对数恒等式和阶乘误差，不提出经典标量公式的优先权主张。

令 $\ell=\log x\ge1$、$r=\log s\ge\ell$、$L=\log2$，并令

$$
c_\ell=\ell^{-1}-\log\ell-1,\quad d_\ell=\ell^{-1}+\ell-1,
\qquad F_\ell(r)=r\log r+c_\ell r+d_\ell-r^{-1}.
$$

对每个 $r>0$ 定义完整有符号积分

$$
E(r)=\int_1^\infty\frac{\eta(y)}{y^2}
\left[(r+\log y)^{-1}+(r+\log y)^{-2}\right]dy.
\tag{FD.3}
$$

**命题 471.1。** 上述实际积分绝对可积，并满足

$$
Q_x(s)=F_\ell(r)+E(r),\qquad
|E(r)|\le2(r^{-1}+r^{-2}).
\tag{FD.4}
$$

**证明。** 在 $x<t<s$ 使用 FD.2 的低域式，再令 $u=\log t$，得到

$$
s\int_x^s\eta(t/s)w(t)\,dt
=\int_\ell^r[(1+r)u^{-2}+r/u-1]du=F_\ell(r).
$$

在 $t>s$ 令 $t=sy$，则原高域恰为 FD.3；$t=s$ 的单点对 Lebesgue 积分无贡献。FD.2 与 $\log y\ge0$ 给出

$$
|\eta(y)|y^{-2}[(r+\log y)^{-1}+(r+\log y)^{-2}]
\le(r^{-1}+r^{-2})(1+\log y)y^{-2}.
$$

完整主控函数的积分 $\int_1^\infty(1+\log y)y^{-2}dy=2$ 支付绝对可积性和上界。低域连续积分可积，故原 $P_x$ 也绝对可积。证毕。

#### 471.2 求导支付的是原有符号高域

**命题 471.2。** 对每个 $r>0$，

$$
E'(r)=-\int_1^\infty\frac{\eta(y)}{y^2}
[(r+\log y)^{-2}+2(r+\log y)^{-3}]dy,
\qquad |E'(r)|\le2(r^{-2}+2r^{-3}).
\tag{FD.5}
$$

**证明。** 固定 $r_0>0$，在邻域 $r_0/2<r<3r_0/2$ 上，逐点导数的绝对值不超过

$$
(4r_0^{-2}+16r_0^{-3})(1+\log y)y^{-2}.
$$

该函数在完整 $(1,\infty)$ 可积，$\eta$ 可测，基点的原积分可积。参数积分求导定理因此适用；积分导数的上界再由积分为 $2$ 得出。这里 $\eta(y)$ 始终是固定乘子，没有对阶乘、floor 或 FD.4 的误差不等式求导。证毕。

同一实际 dyadic 权满足

$$
b_x(s)=F_\ell(r)-\tfrac12F_\ell(r+L)+E(r)-\tfrac12E(r+L).
\tag{FD.6}
$$

其中 $1/2$ 来自 $sP_x(2s)=Q_x(2s)/2$，不能删去。对 $s>x$ 求导，得到

$$
sb'_x(s)=S_\ell(r)+E'(r)-\tfrac12E'(r+L),
$$
$$
S_\ell(r)=\tfrac12\log(r/\ell)+\frac1{2\ell}
-\tfrac12\log(1+L/r)+r^{-2}-\tfrac12(r+L)^{-2}.
\tag{FD.7}
$$

这是对实际 $b_x$ 的恒等式。由 FD.5，完整高域导数误差满足

$$
|sb'_x(s)-S_\ell(r)|\le3r^{-2}+6r^{-3}.
\tag{FD.8}
$$

因为 $0<L<1$、$\log(1+L/r)\le L/r$ 和 $r\ge\ell\ge1$，

$$
0\le\tfrac12\log(r/\ell)+\frac{1-L}{2\ell}
\le S_\ell(r)\le\tfrac12\log(r/\ell)+\frac1{2\ell}+r^{-2}.
$$

故得到完整且显式的导数预算

$$
\boxed{|sb'_x(s)|\le\tfrac12\log(r/\ell)+\frac1{2\ell}+4r^{-2}+6r^{-3}
\le\tfrac12\log(r/\ell)+\frac{21}{2\ell}.}
\tag{FD.9}
$$

固定 $x$ 时，该界为 $|b'_x(s)|=O_x(\log\log s/s)$；固定 $u>1$ 而取 $s=ux$ 时，它为 $O_u(1/(s\log x))$。

**推论 471.3。** 若 $x\ge\exp22$，则实际 $b_x$ 在 $(x,\infty)$ 严格递增。

**证明。** FD.7–FD.8 给

$$
sb'_x(s)\ge\tfrac12\log(r/\ell)+\frac{1-L}{2\ell}-3r^{-2}-6r^{-3}.
$$

使用经典 $\log2<7/10$，非对数部分在 $\ell\ge22$ 时至少为

$$
\frac{(3/20)\ell^2-3\ell-6}{\ell^3}\ge\frac3{5\ell^3}>0.
$$

分子在 $[22,\infty)$ 递增，并在 $22$ 等于 $3/5$。因此导数严格为正，由中值定理得到结论。权的正导数不确定 Möbius 加权尾的符号。证毕。

#### 471.3 对固定 x 支付全部端点、变差与原整数截止

令 $G(n)=\sum_{1\le d\le n,\ d\text{ odd}}\mu(d)/d$ 为实际奇数调和 Möbius 前缀。假定某个算术估计已给出 $A\ge0$、$p>1$ 和整数 $D>x$，使

$$
|G(n)|\le A/(\log n)^p\qquad(n\ge D).
\tag{FD.10}
$$

这是本命题的显式算术前提；有限全截止界 $|G(n)|\le4$ 不推出它。令 $q=\log R$，直接代换 $u=\log t$ 并作完整分部积分，得到

$$
I(R):=\int_R^\infty
\frac{\tfrac12\log(\log t/\ell)+21/(2\ell)}{t(\log t)^p}dt
=q^{1-p}\left[\frac{\log(q/\ell)}{2(p-1)}
+\frac1{2(p-1)^2}+\frac{21}{2\ell(p-1)}\right].
\tag{FD.11}
$$

该公式对 $R\ge x$ 成立；无穷端点 $u^{1-p}\log u\to0$ 由 $p>1$ 支付。对每个整数 $n\ge D$，FD.9 在完整 $[n,n+1]$ 上成立。令其连续非负主控函数为 $m(t)$，对 $b_x\pm\int m$ 应用导数符号与中值定理，得到 $|b_x(n+1)-b_x(n)|\le\int_n^{n+1}m(t)dt$。这一步不要求另行假定 $b'_x$ 连续。

又 $\log t\le2\log n$ 对 $n\le t\le n+1$、$n\ge D>e$ 成立，因此

$$
\sum_{n>D}|G(n)|\,|b_x(n+1)-b_x(n)|\le A2^p I(D+1)<\infty.
\tag{FD.12}
$$

由 FD.4–FD.6，固定 $x$ 时 $b_x(s)=O_x(\log s\log\log s)$，所以 FD.10 支付完整终端 $b_x(M)G(M)\to0$。对每个自然截止 $M>D$，原有限 Abel 恒等式为

$$
\sum_{\substack{D<n\le M\\n\text{ odd}}}\mu(n)[P_x(n)-P_x(2n)]
=b_x(M)G(M)-b_x(D+1)G(D)
-\sum_{n=D+1}^{M-1}[b_x(n+1)-b_x(n)]G(n).
\tag{FD.13}
$$

这里偶数系数为零，$G$ 仍保留所有整数截止；$M=D+1$ 时内部和为空。FD.12 和终端极限证明原自然截止极限 $T_D(x)$ 存在，且

$$
T_D(x)=-b_x(D+1)G(D)-\sum_{n>D}[b_x(n+1)-b_x(n)]G(n),
$$
$$
|T_D(x)|\le|b_x(D+1)|\,|G(D)|+A2^p I(D+1).
\tag{FD.14}
$$

第二个级数绝对收敛；原 Möbius 原子序列只证明按自然截止收敛，没有声称无条件或绝对可和。原 signed anchor $-b_x(D+1)G(D)$ 和整个无限尾均被保留。

这一充分对数幂门槛是 $p>1$。此前粗主控 $(1+\log s)^2/s$ 会要求 $p>3$；FD.9 改变了所需算术供应的强度，但没有构造 FD.10，也没有证明 $p>1$ 是必要条件。

#### 471.4 固定域机制与 RH 临界尺度的界限

固定域代换把全部阶乘跳跃放入与 $r$ 无关的 $\eta(y)$，把参数变化放入可求导、可主控的实际权核。因此准确有符号积分保留下来，同时完整导数可估计。这与有限 Möbius 剥离保留实际前缀和端点的做法相容：重组改变待控接口，不消除算术抵消义务。

对 $D$ 与 $x$ 可比的临界问题，若同一个固定 $A>0$、有限 $p>1$ 的算术界用于 $x\to\infty$，FD.11 给 $I(D+1)=\Theta_p((\log x)^{1-p})$。因此 FD.14 中这一绝对上界项乘以目标 $\sqrt{x}\log x$ 后为 $\Theta_{A,p}(\sqrt{x}(\log x)^{2-p})$，这条估计无法推出临界误差消失；这不是原有符号尾不消失的断言。固定 $x$ 的尾收敛、权的正导数与临界有符号补偿是不同的数学结论。原 prime panel 与其补集的完整有符号补偿以及 RH 的最终符号仍待证明。

## 追加锚（本行以下为增补区）

---

## 472. 外部 RH 库接入口：有限 Euler 剥离可逆，统一储备另需证明

OpenAI/math 固定版本 `adc7f1241b42e322a6451854ab7e4b4c146bf78a` 的 `OAI/NumberTheory/DirichletL/EulerFactors.lean` 给出有限带权 Euler 因子的非零和零点运输。普通 ζ 的同类结论已有本库 `PrimeAddress.finite_prime_modification_preserves_global_zero_set` 与 `EulerWindows.finite_euler_window_ne_zero`，应直接复用。本节仅使用这些有限因子性质，不以 OpenAI 的完整 $7/8$ 主链作为已验收供应。

**定义 472.1（有限带权修改）。** 对有限素数集 $S$、复系数 $|a_p|\le1$，令 $E_S(s)=\prod_{p\in S}(1-a_pp^{-s})$，其中 $p^{-s}=\exp(-s\log p)$。

**定理 472.2（有限级定量可逆性）。** 若 $\operatorname{Re}s\ge\sigma>0$，则

$$
|E_S(s)|\ge\prod_{p\in S}(1-p^{-\sigma})>0,
\qquad |E_S(s)^{-1}|\le\prod_{p\in S}(1-p^{-\sigma})^{-1}.
$$

*证明。* 对每个 $p$，有 $|a_pp^{-s}|=|a_p|p^{-\operatorname{Re}s}\le p^{-\sigma}<1$。反三角不等式给 $|1-a_pp^{-s}|\ge1-p^{-\sigma}>0$，再取有限乘积和倒数。空集给两端恰为 $1$。因此同一实际身份 $L_S=E_SL$ 双向保持这个半平面内的零点。

**定理 472.3（有限可逆性不支付增长素数集的统一逆界）。** 固定 $0<\sigma\le1$，令 $S_P=\{p\le P:p\text{ 为素数}\}$。在允许的实际输入 $a_p=1,s=\sigma$ 上，$E_{S_P}(\sigma)\to0$，故其倒数趋于正无穷。

*证明。* 每个因子为正，由 $\log(1-u)\le-u$，

$$
\log E_{S_P}(\sigma)\le-\sum_{p\le P}p^{-\sigma}\le-\sum_{p\le P}p^{-1}\longrightarrow-\infty.
$$

最后一步复用素数调和级数发散；Mathlib 原供应为 `not_summable_one_div_on_primes`。对一般复系数，这个比较只说明保证下界趋零，不能推出实际乘积趋零；上述实际输入专门证明了全体允许输入上的统一正下界不存在。

固定 $\sigma>1$ 时，$\sum_p p^{-\sigma}<\infty$，且 $0\le-\log(1-p^{-\sigma})\le p^{-\sigma}/(1-2^{-\sigma})$，所以保证下界的无限乘积有严格正极限。临界开带的有限零点运输与绝对收敛半平面的统一逆界有不同的解析门槛。

这给“等价形态像群”的直觉一个可检验版本：有限非零乘子的乘除可组合、可逆，保存零点；相应范数常数随素数集增长，不能由可逆性自动控制。§470 的商块范数增长与这里的 Euler 逆界缺口指向同一问题：把有限层之间的精确关系提升到无界层，需要支付实际输入上的抵消或统一储备。

Gaussian 的完整 Möbius 调和衰减是 §471 固定 $x$ 变差与端点的候选算术供应；它仍须经过准确的全体／奇数传输和本库核验。固定 $x$ 的收敛也不支付共同临界尺度上的有符号补偿。以上关系未建立 $5040$、Fibonacci 与拓扑例外的数值同构，亦未证明 Robin 最终符号或 RH。

## 追加锚（本行以下为增补区）

## 473. §472 引文定位勘正

所引固定版本的正确仓库相对路径为 [`lean/OAI/NumberTheory/DirichletL/EulerFactors.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean)；原引文省略了 `lean/` 前缀。本增补仅修正文献定位，不新增数学内容，也不补足算术或权重桥梁。

## 追加锚（本行以下为增补区）

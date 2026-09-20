# 递归关系观察：可执行上下文几何

空间拼接、时间接续和记忆更新都可以作为带输入输出的关系操作。要用一份几何比较这些操作，首先必须固定哪些上下文实际允许执行，以及一个上下文怎样接到另一个上下文之后。本卷以有类型的配置、允许箭头和带度量的读数为共同数据，构造保留全部指定行为、满足指定增益的最小扩展伪度量。任意参数的笛卡尔代数是它的一种特化；取得常量、复制资源和拼接共同来源的权限则由实际语言决定。

[RRO主卷](RECURSIVE_RELATIONAL_OBSERVATION.md) 第120节给出精确实验行为与最小表示，第121节研究保留式档案、观察核细化与正交信息增量，第122节区分取反的保持、乘法的弱化与投影边界耦合，第124节保留共同来源，第125–128节研究线性响应、记忆和概率，第133–136节研究运输与资源。本卷增加这些接口在有限误差下的组合条件。一个距离由全部允许实验定义，不代表观察者已经执行这些实验；有限预算的可取得部分在第7节另行构造。

## 1. 配置、允许箭头与失败

**定义 1.1（带增益的有类型实验语言）。** 设 $S$ 为类型集合。每个类型 $s$ 有配置集合 $X_s$；配置包括当前任务所需的对象、记录、共享来源与资源状态。每个允许生成箭头 $h:s\to t$ 指定一个总函数
$$
h:X_s\to X_t
$$
和有限正增益 $L_h>0$。每个类型有一族基础读数 $f:X_s\to Y_f$，其中 $Y_f$ 配扩展度量 $\rho_f:Y_f\times Y_f\to[0,\infty]$：对称、满足三角不等式，且 $\rho_f(u,v)=0$ 当且仅当 $u=v$。普通有限值度量是其特例。

一个允许上下文 $C:s\to t$ 是类型匹配的有限箭头路径。空路径是恒等上下文。路径作用取函数复合，增益取乘积：
$$
\ell(\mathrm{id}_s)=1,\qquad
\ell(C\circ h)=\ell(C)L_h.
$$
一个闭实验是上下文 $C:s\to t$ 后接基础读数 $f:X_t\to Y_f$。所有生成箭头与读数构成集合，所以以下测试上确界具有固定索引集合。相同函数的两条执行路径可以具有不同的增益或代价，在这些数据被证明可识别之前不将路径合并。

此处 $L_h$ 是所研究接口指定的增益要求；不预先假定任意给定的有限状态度量都满足它。第2节证明何时存在最小的兼容距离，以及不相容要求怎样导致无穷距离。严格正性用于路径除法；常值操作可以使用任意经过验证的正上界，并不因此失去其实际零变化性质。

**约定 1.2（部分动作的总化）。** 对部分动作 $h:D_h\to X_t$，可以在各类型加入声明的失败结果，将域外输入送往相应失败标签；失败之后的接续按明确的传播或恢复规则定义。成功、失败和任务所需原因进入读数。也可以使用共同定义域作为类型，但接续必须确实保持相应类型。把两个各自合法的输入拼成一个元组，需要另证这个元组合法。

这些总函数描述一次协议怎样作用于任一候选配置，不赋予在未知配置上提前读取隐藏信息的权限。例如自适应策略可以根据已经读到的历史选择下一步；它不能根据未读到的变量选择分支。所需策略状态可纳入配置，已声明的策略作为允许箭头。所有未来允许路径与某一条已经执行的历史是不同的对象。

**命题 1.3（成对删除失败会破坏伪度量）。** 若比较两个配置时只保留对二者都成功的实验，所得成对测试上确界不一定满足三角不等式，也不一定产生传递的零距离关系。

**证明。** 取 $X=\{a,b,c\}$，当前读数恒定，另有部分实验 $e$ 满足 $e(a)=0,e(c)=1$，在 $b$ 处失败。输出用离散距离。只比较双方成功的实验，并把空族上确界取零，得到
$$
d(a,b)=0,\qquad d(b,c)=0,\qquad d(a,c)=1.
$$
所以 $d(a,c)>d(a,b)+d(b,c)$，同时 $a,b$ 与 $b,c$ 零距离而 $a,c$ 非零距离。此处每一对输入使用了不同的测试索引集合。将失败保留为单独结果，才能对同一个测试函数拉回度量。$\square$

**命题 1.4（准入边界不由数值接近自动保持）。** 设实数状态上的动作在 $x\ge0$ 时成功、在 $x<0$ 时失败，成功与失败的输出距离为一。它相对于输入的通常距离不存在全局有限 Lipschitz 常数。

**证明。** 对任意 $\varepsilon>0$，输入 $\varepsilon,-\varepsilon$ 的距离是 $2\varepsilon$，输出距离是一。若有统一有限常数 $L$，则所有 $\varepsilon>0$ 都满足 $1\le2L\varepsilon$，矛盾。$\square$

若任务要求合法性完全保持，可把域保持作为精确关系运输，或给成功与失败之间无穷距离。若选有限处罚，得到的是对应处罚下的近似保证，仍须用实际误差与准入间隔证明某次动作不会跨界。

## 2. 最小上下文距离与递归闭合

**定义 2.1（完整上下文距离）。** 对 $x,y\in X_s$，置
$$
D_s(x,y)=\sup_{\substack{C:s\to t\\f:X_t\to Y_f}}
\frac{\rho_f(f(Cx),f(Cy))}{\ell(C)}.
\tag{2.1}
$$
空测试族的上确界取零。每条有限路径的增益均有限且严格正，因此除法没有零分母；$D_s$ 可以取无穷值。

**定理 2.2（最小增益兼容几何）。** 定义2.1满足：

1. 每个 $D_s$ 是扩展伪度量。
2. $D_s(x,y)=0$ 当且仅当全部允许闭实验在 $x,y$ 上取得相同结果。
3. 每个基础读数满足 $\rho_f(fx,fy)\le D_s(x,y)$，每个允许生成箭头满足
$$
D_t(hx,hy)\le L_hD_s(x,y).
\tag{2.2}
$$
4. 若另一扩展伪度量族 $p_s$ 使全部基础读数为 $1$-Lipschitz，并使每条允许箭头满足相同的 $L_h$ 界，则 $D_s\le p_s$ 逐点成立。

因此 $D$ 自身满足所列要求，并且是满足这些要求的逐点最小者。一份全域有限的合格 $p$ 也给出 $D$ 全域有限的证书。

**证明。** 对固定实验 $(C,f)$，把 $\rho_f$ 沿 $f\circ C$ 拉回，再乘正数 $1/\ell(C)$，得到扩展伪度量。其上确界仍在对角线为零且对称。对任意 $x,y,z$，每一项满足
$$
\frac{\rho_f(fCx,fCz)}{\ell(C)}
\le D_s(x,y)+D_s(y,z),
$$
取上确界得到三角不等式，包括无穷值的情况。全部项非负，且读数度量分离点，所以零上确界等价于每个实验结果相等。恒等上下文给基础读数界。

对箭头 $h:s\to t$ 和输出实验 $(C,f)$，$C\circ h$ 仍是允许上下文，且 $\ell(C\circ h)=\ell(C)L_h$。于是
$$
\frac{\rho_f(fChx,fChy)}{\ell(C)}
\le L_hD_s(x,y).
$$
对输出实验取上确界得到式(2.2)。若 $p$ 满足同样的生成箭头条件，对路径长度归纳得到 $p_t(Cx,Cy)\le\ell(C)p_s(x,y)$。基础读数条件继而给每个实验的归一化差不超过 $p_s(x,y)$，取上确界得 $D_s\le p_s$。$\square$

**命题 2.3（递归闭合与有限深度）。** 令
$$
o_s(x,y)=\sup_{f:X_s\to Y_f}\rho_f(fx,fy),
$$
并在所有类型上的非负扩展值二元函数族 $p$ 上定义
$$
(\mathcal Tp)_s(x,y)=
\max\left\{o_s(x,y),
\sup_{h:s\to t}\frac{p_t(hx,hy)}{L_h}\right\}.
\tag{2.3}
$$
记 $D^{[N]}$ 为式(2.1)中只取长度至多 $N$ 的路径所得距离。则
$$
D^{[0]}=o,\qquad D^{[N+1]}=\mathcal T D^{[N]},
\qquad D=\sup_{N\ge0}D^{[N]},\qquad D=\mathcal TD.
\tag{2.4}
$$
而且 $D$ 是所有满足 $\mathcal Tp\le p$ 的非负扩展值函数族中逐点最小者，故也是 $\mathcal T$ 的最小不动点。

**证明。** 长度至多 $N+1$ 的路径要么为空，要么有首箭头 $h$，其后长度至多 $N$。相应增益分解为 $L_h$ 乘剩余路径增益，故测试上确界恰为式(2.3)。每条允许路径有限，所有路径是各有限深度族之并，因此 $D=\sup_ND^{[N]}$。把完整路径同样按空路径和首箭头分解，得 $D=\mathcal TD$。

若 $\mathcal Tp\le p$，则 $o\le p$ 且每条箭头的拉回满足 $p_t(hx,hy)\le L_hp_s(x,y)$。沿每条有限路径归纳后，用 $o\le p$ 得该路径的实验贡献不超过 $p_s(x,y)$，取上确界得 $D\le p$。此步甚至不需要竞争函数 $p$ 预先满足伪度量律。$\square$

式(2.3)将“当前能区分什么”与“允许操作后还能区分什么”放进同一个闭合规则。它关于这份语言的实验行为，不是物理系统停止变化的不动点。 主卷第121节的累计档案增长描述已取得记录及其可见空间的扩展；本卷路径上确界描述指定语言中全部允许实验的分离能力。允许一种实验、实际取得一次读数、保留这次记录是不同条件。主卷第122节的条件期望保留取反而可能破坏乘法，属于带共同概率律的投影接口；本卷的度量零核本身不替代该乘法缺陷和边界耦合。

**命题 2.4（增益与语言的单调性）。** 在相同实验语言上，若逐生成箭头增加增益 $L_h\le L'_h$，则 $D'\le D$，且两者具有相同零核。在保持旧路径及其增益不变的条件下增加允许箭头或基础读数，则完整距离不减，零核只会缩小。

**证明。** 前一种变化使每条路径分母不减，所以每个实验贡献不增；严格正有限的分母不改变某个贡献是否为零。后一种变化使旧测试族包含于新测试族，其上确界不减，实验相等的条件相应增强。$\square$

**命题 2.5（有限性不能靠指定收缩获得）。** 存在当前可区分的两个点、恒等更新 $h=\mathrm{id}$，使任何指定的 $0<L_h<1$ 都让其完整上下文距离为无穷。

**证明。** 设一个当前读数差为 $c>0$。长度 $n$ 的恒等更新路径具有增益 $L_h^n$，其贡献为 $cL_h^{-n}$。这些值无上界，故 $D(x,y)=\infty$。$\square$

因此较小增益是更强的兼容要求。它可能要求把某些可区分配置置于无穷远，不能免费把一个实际不收缩的过程变成有限距离中的收缩过程。

## 3. 行为商与保真辅助运输

**定义 3.1（实际行为像）。** 对每个类型，令
$$
\beta_s(x)=\bigl(f(Cx)\bigr)_{(C,f)},
\qquad Q_s=\beta_s[X_s].
$$
定义 $x\sim_sy$ 当且仅当 $D_s(x,y)=0$。实际行为像只包含由某个合法配置实现的实验结果族。

**定理 3.2（零核商的规范距离）。** $\sim_s$ 是等价关系，并有自然双射 $X_s/{\sim_s}\cong Q_s$。公式
$$
\overline D_s(\beta_sx,\beta_sy)=D_s(x,y)
\tag{3.1}
$$
在 $Q_s$ 上定义良好的扩展度量。每条允许箭头唯一下降为 $\overline h:Q_s\to Q_t$，满足
$$
\overline h\,\beta_s=\beta_t h,
\qquad
\overline D_t(\overline h b,\overline h b')\le L_h\overline D_s(b,b').
$$

**证明。** 扩展伪度量的零距离由三角不等式成为等价关系；定理2.2将它识别为全部实验读数的共同核，从而得到所述商与实际像双射。若 $D(x,x')=D(y,y')=0$，两次三角不等式给 $D(x,y)\le D(x',y')$ 和反向不等式，故式(3.1)与代表无关。零距离的两个实际行为必相同，所以它是扩展度量。由式(2.2)，零距离输入在 $h$ 后仍零距离，因而按代表定义 $\overline h(\beta_sx)=\beta_t(hx)$ 良好；实际像保证唯一性，增益界直接由式(2.2)得到。$\square$

若另有实际像表示 $q_s:X_s\twoheadrightarrow B_s$，且基础读数和全部允许箭头都通过 $q$ 下降，那么每个路径实验经归纳也通过 $q$ 因子化。因此 $q_s(x)=q_s(y)$ 蕴含 $\beta_s(x)=\beta_s(y)$，并有唯一满射 $B_s\to Q_s$ 与这些读数、操作相容。这是RRO第120节的精确最小表示判据；式(3.1)同时给它由实验增益确定的几何。集合上的因子化本身不提供恢复算法或稳定常数。

**定理 3.3（相同实验语言下的等距运输）。** 给两套定义1.1的实现 $X_s,\widetilde X_s$，使用同一个有类型生成箭头图、同一组基础读数标签、同一读数值域与度量，以及相同的增益。设映射 $r_s:\widetilde X_s\to X_s$ 满足
$$
r_t\widetilde h=h r_s,\qquad \widetilde f=f r_s
\tag{3.2}
$$
对全部生成箭头和基础读数成立，且两套实验都恰由这些生成数据形成。则
$$
\widetilde D_s(\widetilde x,\widetilde y)
=D_s(r_s\widetilde x,r_s\widetilde y).
\tag{3.3}
$$
这不要求 $r_s$ 单射或满射。若各 $r_s$ 满射，则两套实际行为商通过 $\widetilde\beta_s(\widetilde x)\mapsto\beta_s(r_s\widetilde x)$ 等距同构。

**证明。** 对同一个路径词归纳，式(3.2)给 $r_t\widetilde C=C r_s$。因此每个对应实验的结果相同，增益相同，式(2.1)的每项贡献相同；两边按同一实验索引取上确界，得到式(3.3)。满射时基础行为像也全部被覆盖，零核由式(3.3)相应识别，实际行为商上的映射遂为双射且保持距离。$\square$

式(3.2)需要覆盖实际语言。若 $\widetilde X=X\times Z$，$r$ 为第一投影，辅助读数全部取自 $X$，第二坐标可以被消去；一旦允许独立读取 $Z$，就新增了未被运输的实验。取 $X$ 为单点、$Z=\{0,1\}$，原距离为零，新读数的距离为一，式(3.3)不再成立。

**命题 3.4（路径模拟的单向度量控制）。** 设每个源实验 $(C,f)$ 都能由辅助系统中的一个允许实验 $(\widetilde C,\widetilde f)$ 模拟，在比较的全部辅助配置上满足
$$
\widetilde f(\widetilde C\widetilde x)=f(Cr_s\widetilde x),
\qquad
\widetilde\ell(\widetilde C)\le K_s\ell(C),
$$
其中对应读数使用同一个值域和度量，$0<K_s<\infty$ 与具体实验无关。则
$$
D_s(r_s\widetilde x,r_s\widetilde y)
\le K_s\widetilde D_s(\widetilde x,\widetilde y).
\tag{3.4}
$$

**证明。** 对每个源实验，将相同的读数差除以 $\ell(C)$，再乘除 $\widetilde\ell(\widetilde C)$，得到其贡献至多 $K_s\widetilde D_s$。对全部源实验取上确界即可。$\square$

单向模拟不提供反向界，允许辅助系统额外读取的区别也不会由式(3.4)消失。模拟路径的时间与费用同样应按实际执行计算；函数相同而增益不同，或者一次调用被展开为多次实验，都必须携带相应数据运输。

## 4. 多元拼接与合法替换链

**定义 4.1（全参数多元特化）。** 设每个多元组合是总函数
$$
g:X_{s_1}\times\cdots\times X_{s_m}\to X_t,
$$
并为其第 $i$ 孔指定 $L_{g,i}>0$。若对全部相应类型的旁支参数 $a_j$ 都允许箭头
$$
x\longmapsto g(a_1,\ldots,a_{i-1},x,a_{i+1},\ldots,a_m),
$$
且其增益为 $L_{g,i}$，则称实验语言包含该组合的全部参数平移。零元操作给常量，没有输入孔。

**定理 4.2（全参数的多元增益）。** 在定义4.1的条件下，对全部输入元组有
$$
D_t(g(x_1,\ldots,x_m),g(y_1,\ldots,y_m))
\le\sum_{i=1}^mL_{g,i}D_{s_i}(x_i,y_i).
\tag{4.1}
$$
若整个生成箭头族恰由这些参数平移组成，则第2节构造的距离是使基础读数为 $1$-Lipschitz、每个组合孔具有指定增益的逐点最小扩展伪度量族。若还保留其他生成箭头，最小性同时相对于那些箭头的增益要求成立。

**证明。** 从 $g(x_1,\ldots,x_m)$ 开始，依次把第 $i$ 个孔的值换成 $y_i$。其他孔值在每一步都属于允许固定的参数集合，因此定理2.2控制每一步变化，三角不等式给式(4.1)。当 $m=0$ 时两边都是零。指定各孔的增益与指定全部相应平移箭头的增益是同一要求，所以最小性正是定理2.2的第四项。$\square$

这个全参数模型可以比较任意载体元组，却没有自动证明有限观察者已经取得全部旁支参数。参数可以用于语义上的分离证明，而其实际制备、复制与接入仍是另外的关系。

**命题 4.3（受限常量不保证全代数同余）。** 如果上下文旁支只能由一部分可取得常量生成，完整上下文距离不一定满足其余未允许平移的增益界；即使所有指定增益均为一，零核也不一定是全代数的同余。

**证明。** 取 $X=\{0,1,2\}$，唯一可取得常量是 $0$。定义 $g(1,1)=2$，其余二元输入都输出零；读数为 $f(0)=f(1)=0,f(2)=1$，值域使用离散距离。由结构归纳，全部闭项仍等于零，任何非恒等严格单孔上下文因旁支为零而恒为零。因此受限上下文距离是 $D(x,y)=|f(x)-f(y)|$。但
$$
D(0,1)=0,\qquad
D(g(0,1),g(1,1))=D(0,2)=1.
$$
平移 $g(-,1)$ 不在当前语言内，却会把原来零距离的输入分开。$\square$

**命题 4.4（两点的数值边界）。** 单个类型只含两个点时，受限常量也能使某个未允许平移违反指定的严格小于一的增益。

**证明。** 令 $X=\{0,1\}$，唯一常量为零，$g(x,y)=xy$，读数为恒等映射，两孔均指定增益 $1/4$。任意非恒等受限单孔上下文恒为零，故 $D(0,1)=1$。未允许的平移 $g(-,1)$ 为恒等函数，其所需不等式变成 $1\le1/4$，失败。单点载体的全部点对距离为零，不能给这种反例。$\square$

若可取得集合 $K_s$ 对操作封闭，并且所需旁支值能够同时取得、按声明次数使用，则可将定理4.2限制在这些子载体上。仅仅每个值分别可取得，不保证它们能出现在同一份合法联合配置中。

**命题 4.5（合法混合链）。** 对部分组合 $g:R\to X_t$，其中 $R\subseteq\prod_iX_{s_i}$，设两个合法元组由有限链
$$
\boldsymbol z^0=\boldsymbol x,\quad
\boldsymbol z^1,\ldots,\boldsymbol z^k=\boldsymbol y
$$
连接。要求每个 $\boldsymbol z^j\in R$，第 $j$ 步仅改变第 $i_j$ 孔，且该步固定旁支的允许操作已经满足增益 $L_j$。则
$$
D_t(g\boldsymbol x,g\boldsymbol y)
\le\sum_{j=1}^kL_jD_{s_{i_j}}(z^{j-1}_{i_j},z^j_{i_j}).
\tag{4.2}
$$

**证明。** 对链上每个相邻合法元组使用该步的实际增益界，再沿输出链使用三角不等式。$\square$

若每个孔恰好替换一次，就返回式(4.1)的端点加权和；若必须绕行，则应使用实际链的代价。对所有合法链的上界取下确界仍是有效上界，空链族按无穷计，但这不证明链存在或代价有限。

**命题 4.6（合法端点不足以产生混合链）。** 仅要求两个端点合法，且所有两端都合法的逐孔变化满足增益，不能推出式(4.1)。

**证明。** 取 $X=\{0,1\}$、$R=\{(0,0),(1,1)\}$，定义 $g(i,i)=i$，输出使用离散距离。固定一孔后，合法另一孔值至多一个，所以所有合法逐孔比较都是同一点比较。输入零伪度量满足这些逐孔条件，但两个合法元组输出距离为一，端点加权和为零。中间元组 $(0,1),(1,0)$ 都非法。若将失败读数纳入完整总化模型，输入零伪度量便不再满足那份更强的完整实验条件。$\square$

## 5. 复制、共享变量与共同概率来源

**约定 5.1（一个外部接口与内部扇出）。** 允许上下文只有一份外部输入接口，不意味着内部表达式只能使用该输入一次。若协议允许复制，需把复制作为箭头 $\operatorname{copy}:X\to X\times X$，或直接允许带合法扇出布线的单输入上下文图。联合接口及其后续操作必须与这份复制相容。资源规则不允许的复制，不由集合上存在对角函数自动取得。

在命题4.3的三点模型中，若复制合法，则 $x\mapsto g(x,x)$ 是可执行实验，它区分零与一。此时必须扩展测试族，不能继续使用排除了复制的距离宣称已经覆盖所有实际实验。

**命题 5.2（重复变量的增益按路径相加）。** 在定理4.2的全参数条件下，对二元组合及重复输入有
$$
D_t(g(x,x),g(y,y))
\le(L_{g,1}+L_{g,2})D_s(x,y).
\tag{5.1}
$$
对更一般的有限确定性组合图，在每个节点满足所用多元增益界、共享节点的值被保留复用的前提下，展开为树并对每次使用路径累计增益，给出的确定性误差上界仍然有效；同源误差不需要相互独立。

**证明。** 式(5.1)直接使用式(4.1)，或插入中间值 $g(y,x)$ 后两次应用单孔界。一般有限图可按拓扑顺序求值；展开树的每个共享叶仍读取原图同一个值，因此两种表达的输出逐点相同。每次出现该值时使用同一个误差上界，再沿各路径传播，只增加上界的重复项，没有使用误差独立性。$\square$

以通常距离和加减法为例，$x+x$ 的增益为二；$x-x$ 则恒为零。通用逐孔上界给后者至多 $2\varepsilon$，有效但不紧。改进这种上界需要使用真实的相消关系，不能仅因两次出现同一个名称就删去一条路径的误差。

**命题 5.3（相同边缘不保证拼接误差为零）。** 存在两份输入联合律，各对应边缘完全相同，而同一二元读数的输出律距离为一。

**证明。** 令 $U$ 为公平比特，取
$$
P=\operatorname{Law}(U,U),\qquad
Q=\operatorname{Law}(U,1-U).
$$
两个输入坐标的边缘在 $P,Q$ 下均为公平比特。但 XOR 输出分别恒为零和恒为一，其全变差距离为一。因此不能把两份边缘距离零代入联合操作的误差和式，得出输出误差为零。$\square$

若操作的输入是概率律，联合律必须成为实际输入，或通过共同耦合明确给出。两个边缘上分别达到的最优耦合，不必能够同时实现原来两份联合律。

**命题 5.4（共同耦合上的期望与成功概率）。** 设在同一概率空间上有随机元组 $\boldsymbol X,\boldsymbol Y$，所有距离与输出均可测，并且几乎处处满足
$$
D_t(g\boldsymbol X,g\boldsymbol Y)
\le\sum_iL_iD_{s_i}(X_i,Y_i).
$$
则非负扩展期望满足
$$
\mathbb E D_t(g\boldsymbol X,g\boldsymbol Y)
\le\sum_iL_i\mathbb E D_{s_i}(X_i,Y_i).
\tag{5.2}
$$
若有限个局部证书在事件 $E_i$ 上成立，且 $\Pr(E_i^c)\le\alpha_i$，那么全部证书共同成立的概率至少为 $1-\sum_i\alpha_i$。

**证明。** 第一式由期望单调性和有限非负求和的线性性得到，不需要独立性。第二式由 $\Pr(\bigcup_iE_i^c)\le\sum_i\Pr(E_i^c)$ 得到。$\square$

**命题 5.5（重新抽取不保持共享图的语义）。** 将共享随机节点的两次使用改成两次独立调用，可能改变完整输出分布，即使每个节点的边缘分布不变。

**证明。** 抽取一次公平比特 $U$ 并计算 $U\operatorname{XOR}U$，输出恒为零。改成独立抽取公平比特 $U,V$ 后，$U\operatorname{XOR}V$ 为公平比特。两次调用的单独边缘相同，输出律不同。$\square$

保持语义的展开应复用同一个已取得值，或将完整随机源及消费位置纳入状态并证明展开保持该来源。把一个已缓存样本重复读取，并不会产生第二份独立实验信息。RRO第124、135节关于共同来源与复制碰撞的结论在这里成为误差传播的前提。

## 6. 局部缺陷怎样传到整体

**定义 6.1（近似实现的局部缺陷）。** 在定理4.2的全参数模型中，给同签名实现 $\widetilde X_s,\widetilde g$ 及映射 $r_s:\widetilde X_s\to X_s$，不要求满射或单射。对每个组合，指定有限非负数 $\delta_g$，并要求在实际将使用的全部输入上
$$
D_t\bigl(r_t\widetilde g(\widetilde x_1,\ldots,\widetilde x_m),
g(r_{s_1}\widetilde x_1,\ldots,r_{s_m}\widetilde x_m)\bigr)
\le\delta_g.
\tag{6.1}
$$
这些输入可以限制在一个已经证明在执行中封闭的可达域。对部分操作，式(6.1)中插入的中间元组也必须合法，或按已声明失败规则总化。只在两个实际端点各自合法时检验当前读数，不足以提供式(6.1)。

**定理 6.2（有限树的缺陷传播）。** 给同一有限类型正确的组合树 $\mathcal T$，在两套实现中分别求值。每个对应叶满足
$$
D_s(r_s\widetilde x,x)\le\varepsilon_{\rm leaf}<\infty.
$$
定义有限实数预算
$$
E_{\rm leaf}=\varepsilon_{\rm leaf},\qquad
E_{g(\mathcal T_1,\ldots,\mathcal T_m)}
=\delta_g+\sum_{i=1}^mL_{g,i}E_{\mathcal T_i}.
\tag{6.2}
$$
则根的实际距离不超过 $E_{\mathcal T}$。每个叶误差乘其到根路径的增益积，每个节点缺陷乘其严格上方路径的增益积，再全部相加，得到同一个预算。零元组合的预算是其 $\delta_g$。

**证明。** 对有限树归纳。叶处由假设成立。设内部节点的理想子值为 $x_i$、实现子值为 $\widetilde x_i$，插入 $g(r\widetilde x_1,\ldots,r\widetilde x_m)$，依次使用三角不等式、局部缺陷和式(4.1)，得到
$$
\begin{aligned}
&D_t(r\widetilde g(\widetilde{\boldsymbol x}),g(\boldsymbol x))\\
&\le\delta_g+
D_t(g(r\widetilde x_1,\ldots,r\widetilde x_m),g(x_1,\ldots,x_m))\\
&\le\delta_g+\sum_iL_{g,i}D_{s_i}(r\widetilde x_i,x_i)\\
&\le\delta_g+\sum_iL_{g,i}E_{\mathcal T_i}.
\end{aligned}
$$
零元节点直接使用式(6.1)。反复分配式(6.2)得到路径展开。$\square$

若只知道合法混合链，则在每个节点用式(4.2)替代式(4.1)，使用实际链上各步误差；只有链上这些误差由子预算控制时才能继续递推。定理6.2的简洁端点和式不免除这项义务。

**推论 6.3（终端读取误差）。** 假设对应终端读数取值于同一度量空间，且
$$
\rho_f(\widetilde f(\widetilde z),f(r_t\widetilde z))\le\eta_f
$$
在实际终端状态上成立。则整棵树的最终读数误差至多 $\eta_f+E_{\mathcal T}$。

**证明。** 在两个终端读数之间插入 $f(r_t\widetilde z)$。第一段由 $\eta_f$ 控制，第二段由基础读数的 $1$-Lipschitz 性和定理6.2控制。$\square$

当前读数误差不能代替完整距离缺陷。取两比特配置，当前读第一位，后续允许交换两位。状态 $(0,0),(0,1)$ 当前差为零，交换后的读数差为一。因此某局部替换即使当前输出完全正确，也可能把下一步要读取的关系改变；式(6.1)使用的正是后续允许上下文能揭示的缺陷。

**推论 6.4（时间接续的增益乘积）。** 一元动作链每步增益为 $L_k>0$、有限缺陷预算为 $\delta_k\ge0$，初始预算为 $E_0<\infty$。设实际误差由非负实数预算满足 $E_{k+1}\le L_kE_k+\delta_k$。则
$$
E_n\le
\left(\prod_{k=0}^{n-1}L_k\right)E_0+
\sum_{j=0}^{n-1}\left(\prod_{k=j+1}^{n-1}L_k\right)\delta_j.
\tag{6.3}
$$
若 $L_k\le L$、$\delta_k\le\delta$，则
$$
E_n\le
\begin{cases}
L^nE_0+\delta(1-L^n)/(1-L),&0<L<1,\\
E_0+n\delta,&L=1,\\
L^nE_0+\delta(L^n-1)/(L-1),&L>1.
\end{cases}
\tag{6.4}
$$

**证明。** 定理6.2在一元链上提供所需递推预算。对递推逐次代入得到式(6.3)；它也是离散 Gronwall 乘积公式的直接代入。统一上界后计算有限几何和得到式(6.4)，空乘积与空和保证 $n=0$ 时返回初值。$\square$

式(6.3)的算术部分已由钉版 Mathlib 的 discrete_gronwall_prod_general 覆盖；一元近似半共轭、收缩预算和输出轨迹也已有项目结果。这里需要额外证明的是局部证书的实际定义域、所控制的完整上下文距离，以及多元拼接是否具有合法替换链。

**命题 6.5（两次近似辅助运输）。** 设 $X''\xrightarrow{r_2}X'\xrightarrow{r_1}X$，三套系统具有对应一元操作 $h'',h',h$。设 $0\le K,\delta_1,\delta_2<\infty$，$r_1$ 相对于所选距离是 $K$-Lipschitz，且在实际状态上
$$
D(r_1h'x',h r_1x')\le\delta_1,\qquad
D'(r_2h''x'',h'r_2x'')\le\delta_2.
$$
则复合运输的缺陷不超过 $\delta_1+K\delta_2$。

**证明。** 在 $r_1r_2h''x''$ 与 $h r_1r_2x''$ 之间插入 $r_1h'r_2x''$。第一段由 $K\delta_2$ 控制，第二段由 $\delta_1$ 控制，三角不等式给结论。$\square$

**命题 6.6（正容差不是等价关系）。** 对一般度量，关系 $D(x,y)\le\varepsilon$ 在 $\varepsilon>0$ 时不必传递；两次容差替换一般只能给半径相加的保证。

**证明。** 通常实数距离下，$0,\varepsilon,2\varepsilon$ 的相邻距离均为 $\varepsilon$，端点距离为 $2\varepsilon$。一般地，$D(x,y)\le\varepsilon,D(y,z)\le\eta$ 由三角不等式只推出 $D(x,z)\le\varepsilon+\eta$。$\square$

因此零核的精确商不能无条件改成正容差商。近似表示应保留误差大小及其传播关系，而不是把一串各自“足够近”的状态直接认作同一个等价类。

## 7. 有限深度、有限费用与未读取的上下文

**定理 7.1（深度消耗与统一尾界）。** 定义2.3的有限深度距离满足
$$
D_s^{[N]}\uparrow D_s,\qquad
D_t^{[N]}(hx,hy)\le L_hD_s^{[N+1]}(x,y).
\tag{7.1}
$$
在全参数多元模型中，同样有
$$
D_t^{[N]}(g\boldsymbol x,g\boldsymbol y)
\le\sum_iL_{g,i}D_{s_i}^{[N+1]}(x_i,y_i).
\tag{7.2}
$$
若全部读数空间直径统一不超过 $M<\infty$，且所有生成箭头 $L_h\ge\lambda>1$，则
$$
D_s^{[N]}(x,y)\le D_s(x,y)
\le\max\{D_s^{[N]}(x,y),M\lambda^{-(N+1)}\}.
\tag{7.3}
$$

**证明。** 递增极限已由式(2.4)证明。把长度至多 $N$ 的输出路径前接一个箭头，输入路径长度至多 $N+1$，得到式(7.1)；逐孔替换同样给式(7.2)。每条被截去的路径长度至少 $N+1$，增益至少 $\lambda^{N+1}$，读数差至多 $M$。将上确界分成保留与截去两族，得到式(7.3)。$\square$

**命题 7.2（多一层不能无条件省去）。** 存在一步更新，使式(7.1)在 $N=0$ 时把右侧深度也改为零就失败。

**证明。** 取 $X=\{0,1\}^2$、读数 $f(a,b)=a$，更新 $h(a,b)=(b,0)$，增益一。状态 $x=(0,0),y=(0,1)$ 的当前距离为零，但更新后的当前距离为一。$\square$

**命题 7.3（二进制移位的尾界）。** 令 $X=\{0,1\}^{\mathbb N}$，更新 $T$ 为左移，唯一读数为首位，使用离散距离。指定增益 $L\ge1$，则
$$
D_L(x,y)=\sup_{n\ge0}L^{-n}|x_n-y_n|.
$$
若 $x\ne y$ 且首次差异在位置 $m$，则 $D_L(x,y)=L^{-m}$。特别地 $L=1$ 时完整距离是离散距离；$L>1$ 时式(7.3)的尾界可达到。

**证明。** 路径正是 $T^n$。首次差异之前各项为零，首次差异项为 $L^{-m}$，其后各项不超过它。对给定 $N$，取两序列只在位置 $N+1$ 不同，则 $D_L^{[N]}=0$ 而 $D_L=L^{-(N+1)}$。$\square$

不折扣时，任意有限深度的统一误差仍可为一；折扣后远期差异变轻，但更新允许把距离放大 $L$ 倍。这改变了任务对远期差异的计量，未保持同一份不折扣的统一精度要求。该一元公式及首次差异结论已有项目来源，见第8节。

**定义 7.4（包含读取费用的预算距离）。** 给每条生成箭头有限非负费用 $c_h$，路径费用相加，空路径费用为零；给每个基础读数有限非负费用 $c_f$。完整实验费用为
$$
b(C,f)=c(C)+c_f.
$$
在固定共同实验语言中，定义
$$
D_s^{\langle B\rangle}(x,y)=
\sup_{\substack{C:s\to t,\ f\\b(C,f)\le B}}
\frac{\rho_f(fCx,fCy)}{\ell(C)},\qquad B\ge0.
\tag{7.4}
$$
每条路径与读数费用均有限，因此 $D_s=\sup_{B\ge0}D_s^{\langle B\rangle}$。这里使用对该共同配置类型成立的费用合同；状态依赖的准入与资源消费可纳入配置，或使用统一的费用上界，不按每一对状态临时删除测试。

**定理 7.5（接续需要增加输入预算）。** 对费用 $c_h$ 的箭头 $h:s\to t$，有
$$
D_t^{\langle B\rangle}(hx,hy)
\le L_hD_s^{\langle B+c_h\rangle}(x,y).
\tag{7.5}
$$
若 $B\ge c_h$，等价地有 $D_t^{\langle B-c_h\rangle}(hx,hy)\le L_hD_s^{\langle B\rangle}(x,y)$。两边保留相同预算的式子一般不成立。

**证明。** 每个输出实验 $(C,f)$ 的费用至多 $B$；前接 $h$ 后费用为 $c_h+b(C,f)\le B+c_h$，增益乘 $L_h$。因此输入预算族包含全部以 $h$ 开头的拉回实验，取上确界得到式(7.5)。它一般还包含其他实验，故这里只有所述方向的不等式。反例用命题7.2，令更新费用一、读数费用零，预算零即可。$\square$

若实际费用仅有统一上界 $\widehat c_h$，并且相应接续在共同类型上成立，则同一证明给保守预算 $B+\widehat c_h$。单独知道两个端点各自付得起，不足以替代共同可执行语言。

**命题 7.6（按点对删去超预算实验也会破坏三角）。** 对状态依赖费用，若仅比较在两个端点都付得起的实验，则预算距离不一定是伪度量。

**证明。** 取三点 $a,b,c$，当前读数恒定。一个实验在 $a,c$ 处费用一并分别输出零、一，在 $b$ 处费用二。预算为一时，成对删去付不起的实验给 $D(a,b)=D(b,c)=0,D(a,c)=1$，与命题1.3相同。将“超预算”作为读数标签总化，或固定共同资源类型与统一协议族，才恢复固定测试族的前提。$\square$

**定理 7.7（一般预算尾证书）。** 对每个类型定义
$$
\varepsilon_s(B)=
\sup_{\substack{C:s\to t,\ f\\b(C,f)>B}}
\frac{\operatorname{diam}(Y_f)}{\ell(C)},
\tag{7.6}
$$
其中空族取零，直径允许为无穷。则
$$
D_s^{\langle B\rangle}(x,y)\le D_s(x,y)
\le\max\{D_s^{\langle B\rangle}(x,y),\varepsilon_s(B)\}.
\tag{7.7}
$$
若 $\varepsilon_s(B)\to0$ 且 $D_s$ 在所有点对上有限，则预算距离以相应加性尾界一致逼近完整距离。一个可检验的充分条件是：读数直径统一不超过有限数 $M\ge0$、读取费用统一不超过有限数 $c_*\ge0$，并存在 $\alpha>0$ 使每条允许路径满足
$$
\ell(C)\ge e^{\alpha c(C)}.
\tag{7.8}
$$
此时 $B\ge c_*$ 时有
$$
\varepsilon_s(B)\le M e^{-\alpha(B-c_*)}.
\tag{7.9}
$$

**证明。** 把全部实验分成费用不超过 $B$ 与超过 $B$ 两族。前者给式(7.4)，后者的每一项由式(7.6)控制，得到式(7.7)。若距离有限，$\max\{a,e\}\le a+e$ 给加性尾界。对超预算实验，$c(C)>B-c_f\ge B-c_*$；式(7.8)与统一直径界给每项至多 $M e^{-\alpha(B-c_*)}$，再取上确界得式(7.9)。$\square$

逐生成箭头条件 $L_h\ge e^{\alpha c_h}$ 足以推出式(7.8)，因为路径增益相乘而费用相加；它只是充分条件，证明本身只需要预算外归一化读数差具有趋零上界。增益与费用是不同的数据，不因都标在一条箭头上就自动满足指数关系。允许零费用箭头也不破坏定理7.7，但可能使某一预算内仍有无限多个测试。

**命题 7.8（预算内有限枚举的充分条件）。** 固定初始类型。若每个可达类型只有有限条出箭头和有限个基础读数，且全部箭头费用具有统一下界 $c_h\ge c_0>0$，则任意有限预算 $B$ 内的实验族有限。

**证明。** 路径长度至多 $\lfloor B/c_0\rfloor$。有限分叉按深度归纳给有限条该长度范围内的路径；每个终点的基础读数族也有限，所以闭实验族有限。$\square$

**命题 7.9（深度、费用与有限测试是不同条件）。** 有限深度或有限预算不自动给有限测试族；逐箭头严格正费用也不自动给预算内长度上界。

**证明。** 取无限比特序列类型 $X$，比特类型 $Y$。对每个 $n$ 允许一条箭头 $h_n:X\to Y$ 读取第 $n$ 位，每条费用一、增益一，$Y$ 只有恒等读数且读取费用零。预算一、深度一内已经有无限测试。任意有限测试子族只读取有限坐标，在其他位置首次不同的两序列对这些测试相同，而完整预算内距离为一；所以它们不能给误差小于一的统一有限测试替代。

若只有零费用左移与零费用首位读数，预算零内包含全部有限次左移，仍有无限测试。即使每条箭头费用严格正，也可取类型链 $X_0\to X_1\to\cdots$，每个类型均为比特序列，箭头为左移，费用为 $2^{-n-1}$、增益为一；每个类型有零费用首位读数。从 $X_0$ 出发任意长路径总费用小于一，故预算一内长度无界。$\square$

有限枚举也不保证尾误差趋零：命题7.3中给左移单位费用、单位增益，有限预算只检查有限前缀，完整距离却在任意两个不同序列上为一。因此有限枚举的条件与定理7.7的统一尾证书分别承担不同义务。

## 8. 恢复接口与数学来源

第2节的最小距离由一份可执行语言和增益数据共同决定；第3节证明准确运输这份语言时，其行为商几何随之运输。状态坐标、未来响应和当前预测记忆若满足RRO第120节的精确交织条件，并同时保持本卷读数度量及增益，就属于定理3.3的不同表示。额外的欧氏内积、概率律和物理时间尺度仍须各自运输，不能由行为核相同自动取得。

稳定恢复则要求恢复映射相对于指定输入输出距离具有可控制的增益；恢复公式存在本身不提供该常数。把一个恢复模块接到后续操作前，首先证明它的误差在式(6.1)所用几何中有界，再用有限树或路径预算传播。对一族联合任务，误差证书还须属于同一个联合实现，不能把分别可达的最佳误差直接放进一份共同输出。加权线性恢复与原子代价闭包由伴随卷[恢复几何](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)进一步研究。

本卷的共同结构是有类型的允许路径、读数和可检验的误差关系。它给出相对于指定任务的最小性与保真条件；不要求所有物理模型具有相同的实验语言，也不由任意边界投影推出引力对偶或面积熵定律。

| 数学来源 | 本卷使用的范围 |
|---|---|
| [StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)，contextual_equivalence_is_greatest | 严格部分上下文、失败标签、全部旁支参数及精确最大同余；第1、3、4节保留这些条件，并区别实际可取得语言。 |
| [PartialFunctionDomainObservation](../../../D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.lean)，common_success_domain_refutation | 双方成功时读数相同不足以保持动作定义域；命题1.3将成对删测试的失败明确为三角律反例。 |
| [EvaluationSupremumMinimality](../../../D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality.lean)，evaluation_suprema_are_least_dominating；[DualSupremumPseudometricKernels](../../../D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.lean) | 评价上确界的最小支配及零核组件；任意路径增益与允许箭头的闭合由第2节直接给出。 |
| [CanonicalDiscountedFutureGeometry](../../../D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry.lean)，canonical_discounted_future_geometry；[FirstDifferencePowerLaw](../../../D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw.lean)，first_difference_power_law | 有界读数下一元折扣距离、更新增益与首次差异公式；命题7.3是二进制移位实例。 |
| [FinitePredictionTruncation](../../../D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.lean)，finite_prediction_truncation_formula_and_error | 一元有限预测和几何尾界；第7节另保留路径深度消耗、实际费用与有限枚举的条件。 |
| [IteratedDefectAccumulation](../../../D5/S3/Observer/Naturality/IteratedDefectAccumulation.lean)，iterated_naturality_defect_bound；[ApproximateSemiconjugacyError](../../../D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.lean)，approximate_semiconjugacy_error | 近似交织的一元轨道缺陷与收缩预算；本卷使用同一递推，另证明多元局部证书到树形预算的条件。 |
| [Mathlib DiscreteGronwall](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/DiscreteGronwall.lean)，discrete_gronwall_prod_general | 在递推前提成立后，式(6.3)为非负实数增益下的直接参数代入。 |
| [SemiconjugacyComposition](../../../D5/S3/Observer/MetricGeometry/SemiconjugacyComposition.lean)，semiconjugacy_defect_composition；[MetricEntourageComposition](../../../D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition.lean)，metric_entourage_comp_subset | 两次近似运输的缺陷和式、正容差复合半径相加。 |
| [定量对角化与观察者完成化](QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md) 第24节 | 一元折扣几何、递归表达、截断与近似半共轭的既有正文；本卷不把这些一元结果作为新的缺口。 |
| Matteo Mio、Ralph Sarkis、Valeria Vignudelli，[*Beyond Nonexpansive Operations in Quantitative Algebraic Reasoning*](https://arxiv.org/abs/2201.09087v1)，2022，DOI 10.1145/3531130.3533366 | 为运算指定输入距离提升、再要求非扩张的成熟框架。本卷采用扩展值、异质读数与逐箭头增益；不将论文中有界距离的整个元定理未经对应地直接套用。 |

这些来源分别承担上确界、Lipschitz 组合、精确上下文核与离散误差累积。正文给出的普通数学证明说明它们如何在实际允许语言中接续；数学来源、形式化状态和可执行实验能力是不同的陈述。

## 追加锚（本行以下为增补区）
## 9. 经典概率拼接、记忆增益与可组合恢复

### 9.1 同一联合律、零切片与扩展KL

**定义 9.1（有限实验、扩展KL与条件信息）。** 本节概率恢复部分的随机变量取值于有限非空集合，使用自然对数。对两份概率质量函数$p,q$，定义
$$
D(p\Vert q)=
\begin{cases}
\displaystyle\sum_{x:p(x)>0}p(x)\log\frac{p(x)}{q(x)},
&p(x)>0\Longrightarrow q(x)>0,\\
+\infty,&\text{否则}.
\end{cases}
\tag{9.1}
$$
零质量项按零处理，正质量事件被赋零预测时使用无穷分支。

固定一份$P_{ABC}$。其边缘始终由这份共同律求和得到。仅在$P_B(b)>0$时定义$P_{C|b}(c)=P_{BC}(b,c)/P_B(b)$。如需全定义核，可在零$B$切片任选一行概率；乘回$P_B(b)=0$后所有有关联合律都与选择无关。定义
$$
I_P(A:C\mid B)
=\sum_{b:P_B(b)>0}P_B(b)
D(P_{AC|b}\Vert P_{A|b}P_{C|b}).
\tag{9.2}
$$
在所有条件量中，零概率条件切片均省略。

**引理 9.2（有限支持与非负性）。** 有限载体上，$D(p\Vert q)$有限当且仅当$p$的正支持包含于$q$的正支持；总有$D(p\Vert q)\ge0$，且等号当且仅当$p=q$。式（9.2）总为有限非负数。

**证明。** 支持条件直接来自定义9.1。设该条件成立，以$S=\{x:p(x)>0\}$记正支持。由$-\log u\ge1-u$及其等号条件，
$$
D(p\Vert q)\ge\sum_{x\in S}(p(x)-q(x))=1-q(S)\ge0.
$$
若KL为零，则这两个不等式都取等号，迫使$S$上$q(x)/p(x)=1$，且$q(S)=1$，因此$p=q$；反向立即成立。无穷分支不可能取等号。对式（9.2）的任一正条件行，正联合项的两个边缘均正，故相对乘积边缘的KL有限；有限非负加权和仍有限非负。相应有限条件信息接口为[`ConditionalMutualInformation`](../../../D5/S3/Entropy/Submodularity/ConditionalMutualInformation.lean)中的`conditional_mutual_information_nonneg`与`conditional_mutual_information_eq_entropy_defect`；其首坐标是条件坐标，对本式使用$(B,(A,C))$的次序。证毕。

### 9.2 条件独立拼接及其准确含义

**命题 9.3（共同边缘下的经典拼接）。** 从定义9.1中$P$的两份重叠边缘构造
$$
P^{\mathrm{glue}}(a,b,c)=
\begin{cases}
P_{AB}(a,b)P_{BC}(b,c)/P_B(b),&P_B(b)>0,\\
0,&P_B(b)=0.
\end{cases}
\tag{9.3}
$$
$P^{\mathrm{glue}}$是概率，保留$AB$与$BC$两个边缘，并有
$$
D(P\Vert P^{\mathrm{glue}})
=I_P(A:C\mid B)
=H(P^{\mathrm{glue}})-H(P).
\tag{9.4}
$$
它是在给定两份边缘的相容联合律中唯一的最大熵者；缺陷为零当且仅当$A\perp C\mid B$。

**证明。** 这是主卷定理124.14在同一$P$的边缘上的直接应用。其支持条件是：若$P(a,b,c)>0$，则$P_{AB}(a,b),P_{BC}(b,c),P_B(b)$均正，所以$P^{\mathrm{glue}}(a,b,c)>0$。所有熵与该KL因而有限。CMI零集亦由[`MarkovDataProcessing`](../../../D5/S3/Entropy/Submodularity/MarkovDataProcessing.lean)的`conditional_mutual_information_eq_zero_iff_conditional_product`给出，只约束正质量条件切片。

该结论不声明拼接恢复了原来的共同来源。主卷命题124.15取$B$恒定、$A=C$为公平位，原律给$\Pr(A=C)=1$，拼接律给$1/2$。式（9.4）的熵差只比较同一边缘约束下的两份联合律；其假设没有指定物理耗散过程，故不给产热结论。证毕。

### 9.3 任意恢复核的误差分解

**定义 9.4（只访问边界的经典恢复核）。** 一个候选恢复器是逐行归一化的核$r(c\mid b)\ge0$。它保留已有的$(A,B)$，仅根据$B$生成候选$C$，所得联合律为
$$
Q_r(a,b,c)=P_{AB}(a,b)r(c\mid b).
\tag{9.5}
$$
这是恢复器的无旁路条件：同一个$b$使用同一行$r$，不能暗中访问$a$或未知来源标签。给出一个数学核不等于已取得其参数或已获准物理执行。

**定理 9.5（结构缺陷加恢复核失配）。** 对任意定义9.4的$r$，扩展非负实数中有
$$
\begin{aligned}
D(P_{ABC}\Vert Q_r)
&=I_P(A:C\mid B)
  +D(P_{BC}\Vert P_Br)\\
&=I_P(A:C\mid B)
  +\sum_{b:P_B(b)>0}P_B(b)D(P_{C|b}\Vert r(\cdot\mid b)).
\end{aligned}
\tag{9.6}
$$
这里$(P_Br)(b,c)=P_B(b)r(c\mid b)$。所以
$$
\min_r D(P_{ABC}\Vert P_{AB}r)=I_P(A:C\mid B),
\tag{9.7}
$$
且最小值恰由正$P_B$切片上$r(\cdot\mid b)=P_{C|b}$的核取得；零切片上的行不受约束。

**证明。** 先核对无穷分支。若存在$P_{BC}(b,c)>0$而$r(c\mid b)=0$，则$P_B(b)>0$，并有某个$a$使$P(a,b,c)>0$。该点$Q_r=0$，故式（9.6）左边无穷，右边的第二项及对应条件KL也无穷。第一项有限，因此整条式子是$+\infty=\text{有限数}+(+\infty)$，没有无穷减无穷。

否则$r(c\mid b)>0$在$P_{BC}$的正支持上成立。于是所有需取对数的比值均正。在$P(a,b,c)>0$处有
$$
\frac{P(a,b,c)}{P_{AB}(a,b)r(c\mid b)}
=\frac{P(a,b,c)P_B(b)}{P_{AB}(a,b)P_{BC}(b,c)}
 \frac{P_{BC}(b,c)}{P_B(b)r(c\mid b)}.
$$
取对数、乘$P(a,b,c)$并求有限和。第一项由式（9.4）为$I_P(A:C\mid B)$；第二项先对$a$求和，得到$D(P_{BC}\Vert P_Br)$。再把$P_{BC}=P_BP_{C|b}$代入正$B$切片，约去同一个$P_B$，得到式（9.6）的第二行。$P_B=0$时非负边缘和为零迫使整片$P_{BC}$和$P$均为零，因此不出现任何遗漏项。

所有条件KL非负，选$r=P_{C|B}$并任意补全零行，得到最小值。由于$I_P(A:C\mid B)$有限，等于最小值当且仅当第二项为零；有限和中每个正$P_B$权重的KL均必须为零，即该行$r=P_{C|b}$。

一般组合积的成熟KL链式公式见钉版Mathlib [`KullbackLeibler/ChainRule.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean)中的`InformationTheory.klDiv_compProd_eq_add`：其前提为有限测度及Markov核，证明包括非绝对连续和不可积导致的无穷分支。项目[`Divergence/ChainRule`](../../../D5/S3/Divergence/ChainRule.lean)的`kl_divergence_chain_rule`则要求有限质量函数处处严格正；上面的支持分类明确处理了超出该严格正接口的情形。证毕。

**推论 9.6（对数评分的两层代价）。** 给定完整$(A,B)$的最佳期望对数损失为$H(C\mid A,B)$；只用$B$并实际选取定义9.4的$r$时，其期望损失为
$$
H(C\mid A,B)+I_P(A:C\mid B)
+\sum_{b:P_B(b)>0}P_B(b)D(P_{C|b}\Vert r(\cdot\mid b)).
\tag{9.8}
$$
**证明。** 在每个正条件行展开$-\log r=-\log P_{C|b}+\log(P_{C|b}/r)$，再用有限条件熵链式法则；零预测的分支两边同为无穷。最优评分结论是[ML伴卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理18.2的直接应用。式（9.8）的最小值是在指定核集合上取得的数学值，其前提不包含真实条件律的估计或执行成本。证毕。

### 9.4 保留式记忆追加的精确缺陷收支

**定义 9.7（固定未来目标的记忆缺陷）。** 固定同一份联合律$P_{HF}$，其中$H$是完整历史或所声明的完整来源，$F$是同一个未来任务变量。给确定函数
$$
M=m(H),\qquad Z=g(H),\qquad M^+=(M,Z).
$$
它们都取有限值。若用$M$预测$F$，其条件独立模拟律为
$$
Q_M(h,f)=P_H(h)P_{F|M}(f\mid m(h)),
$$
零$M$切片任选补全；以$M^+$代替$M$同样定义$Q_{M^+}$。记
$$
\Delta_M=D(P_{HF}\Vert Q_M)=I_P(H:F\mid M),
\qquad
\Delta_{M^+}=D(P_{HF}\Vert Q_{M^+})=I_P(H:F\mid M,Z).
\tag{9.9}
$$
等式由式（9.4）在$(H,M,F)$及$(H,M^+,F)$图律上的直接应用得到；去掉由$h$决定的记忆坐标只是对非零项重编号。

**定理 9.8（追加记录恰减少其条件目标信息）。** 在定义9.7下，
$$
\Delta_M=\Delta_{M^+}+I_P(Z:F\mid M),
\qquad
\Delta_M-\Delta_{M^+}=I_P(Z:F\mid M)\ge0.
\tag{9.10}
$$
等号$\Delta_M=\Delta_{M^+}$恰在每个正$M$切片上$Z,F$条件独立时成立。因而增加记录数、增加档案熵和减少本目标的预测缺陷是不同的陈述。

**证明。** 由有限条件熵链式法则，
$$
I(H:F\mid M)=H(F\mid M)-H(F\mid H,M).
$$
由于$M=m(H)$，在每个正$H$切片上，加入$M$不会改变$F$的条件律，故$H(F\mid H,M)=H(F\mid H)$。同理，$(M,Z)$由$H$决定，故
$$
\Delta_M=H(F\mid M)-H(F\mid H),\qquad
\Delta_{M^+}=H(F\mid M,Z)-H(F\mid H).
$$
两式相减给$H(F\mid M)-H(F\mid M,Z)=I(Z:F\mid M)$。全部条件熵有限，因此这里的减法合法。式（9.2）给非负性及条件独立的等号判据。

同一计算还给$I(F;H)=I(F;M)+\Delta_M$与$I(F;M^+)-I(F;M)=I(F;Z\mid M)$，即主卷式（121.27）的残差表达。所用链式法则为[`MutualInformationChainRule`](../../../D5/S3/Entropy/Submodularity/MutualInformationChainRule.lean)中的`mutual_information_chain_rule`；主卷§81.2、§121.9及§127.7具有相同的固定目标、共同联合律条件。此证明没有独立噪声假设。证毕。

**命题 9.9（额外记录依赖其他来源时的修正项）。** 对任意共同有限联合律$(H,F,M,Z)$，不假定$Z$由$H$决定时，有
$$
I(H:F\mid M)-I(H:F\mid M,Z)
=I(Z:F\mid M)-I(Z:F\mid H,M).
\tag{9.11}
$$
**证明。** 将$I((H,Z):F\mid M)$分别按$H$先、$Z$先展开，并移项即得。取独立公平位$H,F$、常值$M$以及$Z=H\mathbin{\mathrm{XOR}}F$，则$I(H:F\mid M)=0$，给定$Z$后$H$决定$F$，所以$I(H:F\mid M,Z)=\log2$。此时$I(Z:F\mid M)=0$而$I(Z:F\mid H,M)=\log2$，验证缺陷可以增加。证毕。

### 9.5 固定策略与恢复器的量词

**定义 9.10（固定策略的共同实验合同）。** 对未来任务变量$F$及控制策略$\pi$，指定完整实验律$P^\pi_{HF}$。策略只能根据已取得的历史自适应选动作，所有随机分支、失败标记和共同来源均保留在该实验中。比较两种摘要时固定同一$\pi$、同一个$F$及同一份联合律；“同一策略”指同一个根据可访问记录选择动作的规则，不允许一侧根据另一侧没有的隐藏变量分支。

若协议使用随机种子，依主卷§121.10将种子及实际数据的共同来源纳入完整模型；是否写入可访问档案另行指定。扩展$H$后使用定义9.7时，完整来源及全部条件量按扩展后的同一联合律定义，不混用不同$H$对应的缺陷。

**推论 9.11（逐策略增益与共同策略族的最坏缺陷）。** 在定义9.10中，对每个固定合法策略$\pi$及同一确定摘要$M=m(H),Z=g(H)$，有
$$
\text{对每个固定合法 }\pi,\qquad
\Delta_M^\pi=\Delta_{M^+}^\pi+I_{P^\pi}(Z:F\mid M).
\tag{9.12}
$$
若同一个策略族$\Pi$在两种表示下都合法，而且每个$\pi$的共同实验律已给定，则
$$
\sup_{\pi\in\Pi}\Delta_{M^+}^\pi
\le\sup_{\pi\in\Pi}\Delta_M^\pi.
\tag{9.13}
$$

**证明。** 对每个$P^\pi$直接应用定理9.8，得到式（9.12）。去掉非负增益项并对同一索引族取上确界，得到式（9.13）。该论证不把两个最坏值之差等同于某个未指定策略的条件互信息；策略族随记忆能力变化时，须先满足本命题的共同索引及合法执行条件。证毕。

**命题 9.12（换策略不能套用同律缺陷差）。** 保留旧记录同时换用另一未来策略后，新旧缺陷不必单调。

**证明。** 令$H=(U,V)$，其中$U,V$为独立公平位，$M$恒定，$Z=U$。策略$\pi_0$使未来目标输出$F_0$恒为零，则$\Delta_M^{\pi_0}=0$。策略$\pi_1$使未来输出$F_1=V$，则
$$
\Delta_{M^+}^{\pi_1}=I((U,V):V\mid U)=\log2.
$$
记录已增加，而跨策略缺陷从零变为$\log2$。这不反驳式（9.12）：在固定$\pi_1$下，旧缺陷也是$\log2$，新增$U$带来的条件目标信息为零。证毕。

**命题 9.13（逐实验恢复与一份通用恢复器不同）。** 即使每个实验的CMI均为零，也不保证存在一份不接收实验标签的核$r(F\mid M)$同时恢复全部实验。

更一般地，对一族已指定实验$i$，存在同一个核$r(c\mid b)$达到各自式（9.7）的最小值，当且仅当所有满足$P_B^i(b)>0$的实验在该$b$上的$P^i_{C|b}$相同。若要求各实验误差都为零，还须各自的CMI为零。

**证明。** 对第一项，令$H,M$都为单点。实验$0$令$F=0$，实验$1$令$F=1$。两实验各自CMI均为零，并分别由核$\delta_0$、$\delta_1$准确恢复。若同一$r$同时恢复两者，则它的一行既等于$\delta_0$又等于$\delta_1$，矛盾。若标签$\pi$本来就是恢复器合法可访问的输入，则可以使用$r(F\mid M,\pi)$；这符合扩充输入类型后的合同。

一般判据的必要性由定理9.5的等号条件得到；充分性是在有质量的$b$上取公共行，在所有实验均零质量的$b$上任选概率行。定理9.5还说明，在达到最小值后误差为零恰要求各自CMI为零。证毕。

### 9.6 支持上的充分性、平均界与最坏情形

**命题 9.14（正支持上的预测充分性）。** 将$P_{HF}$写为$\mu(h)K(f\mid h)$，令$M=m(H)$，则
$$
\Delta_M=0
\iff
\forall h,h',\quad
\bigl[\mu(h)>0,\ \mu(h')>0,\ m(h)=m(h')\bigr]
\Longrightarrow K(\cdot\mid h)=K(\cdot\mid h').
\tag{9.14}
$$
若$\mu$在全部候选历史上全支持，该判据给全域纤维充分性；一般先验只约束其正支持。对每个Dirac先验分别有零缺陷，不能替代一份全支持先验。

**证明。** 式（9.14）直接应用[`ConditionalInformationSufficiency`](../../../D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency.lean)中的`conditional_information_zero_iff_support_sufficiency`，将该声明的`prior`、`kernel`、`concept`依次取为$\mu,K,m$。全支持时，两个正概率前提对全部$h,h'$成立。反之，Dirac条件下$H$恒定，不论$m$怎样丢信息，其缺陷都为零；例如两个历史对应不同的确定未来，常值$m$在各Dirac先验下缺陷均零，却不满足全域纤维充分性。证毕。

**推论 9.15（平均TV界及最坏纤维的反例）。** 对定理9.5中的任意$r$，定义$\operatorname{TV}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$，则
$$
\operatorname{TV}(P,Q_r)
\le\sqrt{\frac{I_P(A:C\mid B)+D(P_{BC}\Vert P_Br)}{2}}.
\tag{9.15}
$$
取$r=P_{C|B}$并按共同$AB$边缘求和，还得到
$$
\sum_{a,b:P_{AB}(a,b)>0}P_{AB}(a,b)
\operatorname{TV}(P_{C|a,b},P_{C|b})
\le\sqrt{I_P(A:C\mid B)/2}.
\tag{9.16}
$$
小CMI不保证同摘要纤维内各历史的未来条件律一致接近。

**证明。** 将[ML伴卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)命题18.3证明中的有限Pinsker不等式$\operatorname{TV}(p,q)\le\sqrt{D(p\Vert q)/2}$应用于$(P,Q_r)$，再代入定理9.5，得到式（9.15）。该Pinsker证明经二元合并与二项KL的二阶导数下界，包含端点和无穷分支；KL无穷时这里只给平凡上界。取$r=P_{C|B}$后，两联合律具有相同$AB$边缘，逐正切片提取权重，得到式（9.16）左侧恰为$\operatorname{TV}(P,P^{\mathrm{glue}})$，故第二式成立。

反例仍取该命题的稀有状态模型：$\Pr(H=1)=\varepsilon\in(0,1)$、$F=H$、$M$恒定时，$\Delta_M=h(\varepsilon)\to0$，而两个历史的真实未来条件律之间TV始终为一。每个先验都有全支持，但正概率下界随$\varepsilon$趋零，故不能推出统一最坏纤维误差。证毕。

### 9.7 进入后续实验所需的共同接口

**命题 9.16（相同随机后处理保存联合误差证书）。** 设两份有限配置律$P,Q$包含后续任务所需的全部共同来源。某一允许后续实验及其读数由同一个逐行归一化核$L(y\mid x)$作用于两份配置。则
$$
\operatorname{TV}(LP,LQ)\le\operatorname{TV}(P,Q).
\tag{9.17}
$$
因此，当本卷定义2.1的所有允许生成箭头均为这样的随机核、读数距离为TV且各增益取一时，由式（9.15）得到完整上下文距离的同一个上界。

**证明。** 逐输出使用三角不等式并交换有限和，
$$
\begin{aligned}
\tfrac12\sum_y\left|\sum_xL(y\mid x)(P(x)-Q(x))\right|
&\le\tfrac12\sum_{y,x}L(y\mid x)|P(x)-Q(x)|\\
&=\tfrac12\sum_x|P(x)-Q(x)|.
\end{aligned}
$$
归一化核的复合仍归一化，所以每个合法有限上下文均满足此界；再对固定实验族取上确界即得结论。

一个有限自适应协议也可写成这种核：给每个可访问历史一行明确的动作随机化和结果转移，沿有限树把联合概率相乘并对内部变量求和，逐层行和为一。必须在两边使用同一协议，并保留成功、失败及协议所需的来源；对成功分支后选择并重新归一化通常不是同一个归一化线性核，不由式（9.17）保证收缩。若人为要求生成箭头具有小于一的增益，也不能由TV收缩直接推出相应归一化完整距离的同一界。

本命题的输入是完整联合律。仅有边缘相同不够，反例由本卷命题5.3给出；只比较一条策略不提供定义2.1完整实验族中的统一条件。若摘要通过ML伴卷定理17.3的联合“输出—后继摘要”核因子化，则可对每个可访问历史归纳，得到同一自适应协议的完整记录律；该卷命题17.7给出分别保留输出和后继摘要边缘仍失败的两步反例。这些条件均保留共同来源，与式（9.17）的完整联合输入要求一致。证毕。

**定义 9.17（关系表示及执行资源合同）。** 一个参与本节恢复比较的关系接口，同时指定配置域、共同来源、允许操作、读数、状态与操作的表示，以及实际调用的非负资源向量。图用于登记合法连接、来源和依赖；矩阵表示已指定的线性映射；张量表示多接口及其已给出的收缩；几何代数使用明确的二次型、分次及乘法；概率核使用非负性和归一化；逻辑接口使用已指定的后承与证书转换。这些表示之间的连接沿用主卷各自的有类型合同：§132.1—132.2的张量割与自动机矩阵，§129的Clifford/外代数及条件协方差投影，§131的外幂/Hodge运输，以及§136.3的保真辅助线和证明运输。

其中主卷§129.7的向量乘法缺陷引用的是平均条件协方差；§129.8将概率质量重建与Clifford线性读出分别定义在概率质量空间和Clifford空间，二者只共享条件投影；§136.3的证明运输使用保持后承、需要时反射后承及证书转换的条件。本合同保留这些原有类型及条件，不把同一矩阵写法视为映射相同或因果次序可交换。

条件律的测量、拟合、存储、核调用、取得额外权重或相干资源，以及实际计时，均作为该合同的额外输入。费用依本卷第7节及恢复几何卷逐资源坐标计账；概率熵、恢复误差和时间费用保留各自单位，定义9.1—9.14不提供这些量之间的兑换率。

### 9.8 递归历史增长在指定距离下的维数

**定理 9.18（禁止长串的首差Hausdorff维数）。** 对整数$k\ge2$，采用主卷§132.2定义的根$\lambda_k$：
$$
\sum_{j=1}^k\lambda_k^{-j}=1,\qquad 1<\lambda_k<2,\qquad\lambda_k\uparrow2
\quad(k\ge2).
\tag{9.18}
$$
令
$$
X_k=\{x\in\{0,1\}^{\mathbb N_0}:x\text{不含连续}k\text{个}1\},
$$
并对$x\ne y$定义
$$
d(x,y)=2^{-\min\{j\ge0:x_j\ne y_j\}},\qquad d(x,x)=0.
$$
则
$$
\dim_{\mathrm H}(X_k,d)=D_k:=\frac{\log\lambda_k}{\log2},
\qquad D_k\uparrow1.
\tag{9.19}
$$
这里Hausdorff测度沿用主卷定义33.0的无额外系数约定，以任意可数覆盖的直径幂和定义；覆盖集不必可测。

**证明。** 主卷§132.2给出合法长度$n$词数$a_n^{(k)}$的$k$阶递推及界$a_n^{(k)}\le C_k\lambda_k^n$，其中$C_k<\infty$；同时给出式（9.18）的根与极限。$k=2$的维数结论亦是主卷定理33.2的精确实例。

共享前缀使$d$满足强三角不等式；它给出二进制乘积拓扑。禁止模式的补集是开柱的并，故$X_k$闭于紧致二进制乘积空间，所以紧致。每个合法有限词后补全零仍合法，故每个合法柱非空。长度$n$柱的直径至多$2^{-n}$，全部$a_n^{(k)}$个柱覆盖$X_k$。因此对任意$s>D_k$，
$$
\mathcal H^s_{d,2^{-n}}(X_k)
\le C_k\lambda_k^n2^{-ns}
=C_k2^{-n(s-D_k)}\longrightarrow0,
$$
给出维数上界。在临界指数$D_k$同样给$\mathcal H^{D_k}_d(X_k)\le C_k$。

下界需要相容概率，不能将每层均匀词分布自动当作同一个无限来源。令状态$i\in\{0,\ldots,k-1\}$记当前末尾连续$1$的数目，初态为$0$。给出正权
$$
r_i=\sum_{j=1}^{k-i}\lambda_k^{-j},\qquad
r_0=1,\quad0<r_i\le1.
$$
当$i<k-1$，有$\lambda_kr_i=r_0+r_{i+1}$；当$i=k-1$，有$\lambda_kr_{k-1}=r_0$。因此以下是逐行归一化的转移：输出$0$并转到$0$的概率为$r_0/(\lambda_kr_i)$；若$i<k-1$，输出$1$并转到$i+1$的概率为$r_{i+1}/(\lambda_kr_i)$。在$i=k-1$时只能输出$0$，其概率为一。其余转移概率为零。

这是对原允许图的Perron正权重加权，即通常的Parry转移构造；此处固定初态$0$，不额外称所构造的词概率平稳。主卷§132.2的计数矩阵按“列输入、行输出”书写，而此处$r$满足其转置的正特征向量方程，故不能误把原右特征向量直接当作这里的行归一化权重。

对合法长度$n$词$w$，其状态路径从$0$唯一确定，末态记$i_n$。沿路径概率相乘，各$r$望远镜相消，得到柱质量
$$
\mu([w])=\frac{r_{i_n}}{\lambda_k^nr_0}
\le\lambda_k^{-n}=2^{-nD_k}.
\tag{9.20}
$$
行和为一使父柱质量恰等于子柱质量之和，空柱质量为一。与主卷定理33.1相同，这在有限柱并的开闭代数上定义相容有限预测度：若不交开闭集之并仍开闭，紧性给有限子覆盖，所以实际只有有限个非空成员，确保该代数上的可数可加性。有限预测度的测度扩张定理因此给$X_k$上的Borel概率$\mu$。由式（9.20），每个点的质量被$2^{-nD_k}\to0$控制，所以$\mu$无原子。

对任意包含至少两点的$U\subseteq X_k$，在其不同点对的首差下标中取最小值$m$。所有点共享前$m$位，且存在两点在第$m$位不同，所以$\operatorname{diam}_dU=2^{-m}$，而$U$包含于一个长度$m$柱。于是外测度满足
$$
\mu^*(U)\le2^{-mD_k}=(\operatorname{diam}_dU)^{D_k}.
$$
空集及单点由无原子性满足同一界。对任意可数覆盖$X_k\subseteq\bigcup_jU_j$，外测度次可加性给
$$
1\le\sum_j\mu^*(U_j)
\le\sum_j(\operatorname{diam}_dU_j)^{D_k}.
$$
故$\mathcal H^{D_k}_d(X_k)\ge1>0$，给出维数下界。与上界合并得到式（9.19）；$D_k\uparrow1$直接由式（9.18）及对数连续严格递增性得到。

下界所用质量分布方法对应钉版Mathlib的[`Measure.le_hausdorffMeasure`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Hausdorff.lean)，其条件是集合质量不超过直径幂；[`dimH_of_hausdorffMeasure_ne_zero_ne_top`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/MetricSpace/HausdorffDimension.lean)给正有限临界测度的维数结论。证毕。

**推论 9.19（距离尺度与词语言的范围）。** 在定理9.18的同一$X_k$上，把距离改成$d_\theta(x,y)=\theta^{\min\{j:x_j\ne y_j\}}$、$0<\theta<1$，并令相等点距离为零，则Hausdorff维数为$\log\lambda_k/(-\log\theta)$。式（9.19）不指定其他物理空间或Hilbert空间的维数，也不适用于任意一条固定合法词的因子语言。

**证明。** 长度$n$柱直径改为至多$\theta^n$，式（9.20）的质量界仍为$\lambda_k^{-n}$。令$s_\theta=\log\lambda_k/(-\log\theta)$，则$\lambda_k^{-n}=(\theta^n)^{s_\theta}$；定理9.18的柱覆盖、任意集合质量界及正有限临界测度证明逐项成立，给出所述维数。它依赖所指定的载体与距离，故不给未指定空间的维数结论。

固定词语言的区别可由[`SubshiftHausdorffDimension`](../../../D5/S1/Words/Complexity/SubshiftHausdorffDimension.lean)中的`dimH_goldenSubshift_eq_zero`见证：该结论研究一条固定黄金词的因子语言，其复杂度线性、Hausdorff维数为零；它的载体不是所有禁止$11$的序列，所以与$D_2>0$的结论适用域不同。证毕。

## 9.99 追加锚

## 10. 量子条件互信息、共用恢复与参考系统

**定义 10.1（有限维量子恢复的对象与距离）。** 以下所有系统均为非零有限维复 Hilbert 空间。记 $\mathcal L(A)$ 为 $A$ 上的线性算子空间，$\mathcal D(A)$ 为密度算子集。量子通道均为完全正且保迹的线性映射，简称 CPTP。对 $\rho_{ABC}\in\mathcal D(A\otimes B\otimes C)$，下标表示相应偏迹边缘，定义
$$
S(\rho)=-\operatorname{Tr}(\rho\ln\rho),\qquad
I(A:C\mid B)_\rho
=S(\rho_{AB})+S(\rho_{BC})-S(\rho_B)-S(\rho_{ABC}),
\tag{10.1}
$$
其中 $0\ln0=0$。本节全部熵使用自然对数。对同一系统上的密度算子，定义根保真度与半迹距离
$$
F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1,\qquad
d_1(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
\tag{10.2}
$$
因此 $F$ 不是某些文献采用的平方保真度 $F^2$。恢复映射的类型固定为
$$
\mathcal R:\mathcal L(B)\longrightarrow\mathcal L(B\otimes C),\qquad
\widehat\rho_{ABC}=(\operatorname{id}_A\otimes\mathcal R)(\rho_{AB}).
\tag{10.3}
$$
恢复比较的是整个 $ABC$ 联合态；系统 $A$ 上保持恒等通道。

**定理 10.2（Fawzi–Renner 恢复界）。** 对每个 $\rho_{ABC}$，存在 CPTP 映射 $\mathcal R:B\to BC$，使
$$
F(\rho_{ABC},\widehat\rho_{ABC})
\ge \exp\!\left[-\frac12 I(A:C\mid B)_\rho\right].
\tag{10.4}
$$
同一个恢复映射满足
$$
d_1(\rho_{ABC},\widehat\rho_{ABC})
\le \sqrt{1-\exp[-I(A:C\mid B)_\rho]}
\le \sqrt{I(A:C\mid B)_\rho}.
\tag{10.5}
$$

这里的结论是 $\rho$ 接近某个从其自身 $AB$ 边缘恢复的态 $\widehat\rho$。定理没有断言 $I(A:C\mid B)_{\widehat\rho}=0$，也没有给出到全部精确 Markov 态集合的同一距离界；这一差别见下引 Fawzi–Renner 论文第1节对近似 Markov 性的讨论。

**证明。** 式(10.4)是 Omar Fawzi、Renato Renner，[*Quantum conditional mutual information and approximate Markov chains*](https://arxiv.org/abs/1410.0664v3)，Theorem 5.1，式(102)的有限维版本。原文熵以二为底，因 $I_{\mathrm{nat}}=(\ln2)I_{\mathrm{bits}}$，其 $2^{-I_{\mathrm{bits}}/2}$ 正好成为式(10.4)。式(10.5)由同文 Lemma B.1 在归一化态上的不等式
$$
d_1(\rho,\sigma)^2\le 1-F(\rho,\sigma)^2
$$
以及 $1-e^{-x}\le x$（$x\ge0$）直接得到。非负性 $I(A:C\mid B)_\rho\ge0$ 是强次可加性。$\square$

**推论 10.3（零条件互信息与精确恢复等价）。** 对有限维三方态，
$$
I(A:C\mid B)_\rho=0
\quad\Longleftrightarrow\quad
\exists\mathcal R:B\to BC\ \mathrm{CPTP},\
(\operatorname{id}_A\otimes\mathcal R)(\rho_{AB})=\rho_{ABC}.
\tag{10.6}
$$

**证明。** 正向由式(10.5)得到半迹距离为零。反向设精确恢复成立。互信息在局部通道下满足数据处理，因此对输入 $\rho_{AB}$ 上的通道 $\mathcal R$ 有
$$
I(A:BC)_\rho\le I(A:B)_\rho.
$$
而熵的链式恒等式给出
$$
I(A:C\mid B)_\rho=I(A:BC)_\rho-I(A:B)_\rho\le0.
$$
结合强次可加性得零。$\square$

**定理 10.4（固定边缘的通用恢复器）。** 固定任意 $\omega_{BC}\in\mathcal D(B\otimes C)$，存在一个 CPTP 映射 $\mathcal R_\omega:B\to BC$，使对每个有限维系统 $A$ 及每个满足 $\rho_{BC}=\omega_{BC}$ 的扩展 $\rho_{ABC}$，都有
$$
F\!\left(\rho_{ABC},
(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})\right)
\ge e^{-I(A:C\mid B)_\rho/2}.
\tag{10.7}
$$
其量词顺序为
$$
\forall\omega_{BC}\ \exists\mathcal R_\omega\
\forall A\ \forall\rho_{ABC}\text{ 满足 }\rho_{BC}=\omega_{BC}.
\tag{10.8}
$$
这是 David Sutter、Omar Fawzi、Renato Renner，[*Universal recovery map for approximate Markov chains*](https://arxiv.org/abs/1504.07251v3)，Theorem 2.1 的有限维、自然对数版本。

同一映射还满足
$$
\mathcal R_\omega(\omega_B)=\omega_{BC}.
\tag{10.9}
$$

式(10.9)约束指定输入 $\omega_B$，并不把 $\operatorname{Tr}_C\circ\mathcal R_\omega$ 规定为整个 $\mathcal L(B)$ 上的恒等通道。式(10.8)也没有将恢复器统一到所有彼此不同的 $BC$ 边缘上。上述来源的 Corollary 2.4 对其显式结构给出线性化保真度界；这里引用的是 Theorem 2.1 的存在性与完整指数界。

**证明。** 对式(10.9)，取任意乘积扩展 $\rho_{ABC}=\rho_A\otimes\omega_{BC}$。其条件互信息为零；式(10.7)及式(10.5)中的保真度到迹距离转换给出精确恢复。对 $A$ 取偏迹即得式(10.9)。这也是原文 Remark 2.3。$\square$

**推论 10.5（固定边缘态族的共同误差）。** 设 $\mathcal F$ 是非空的一族有限维三方态，所有成员具有同一个 $BC$ 边缘 $\omega_{BC}$；参考系统 $A$ 的有限维数可以随成员变化。若存在 $\varepsilon\ge0$ 使
$$
I(A:C\mid B)_\rho\le\varepsilon\qquad(\rho\in\mathcal F),
$$
则定理10.4中的同一个 $\mathcal R_\omega$ 满足
$$
\sup_{\rho\in\mathcal F}
d_1\!\left(\rho_{ABC},
(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})\right)
\le\sqrt{1-e^{-\varepsilon}}\le\sqrt\varepsilon.
\tag{10.10}
$$

**证明。** 对每个成员用式(10.7)及保真度到迹距离转换；函数 $x\mapsto\sqrt{1-e^{-x}}$ 在非负半轴上递增，所以各项由同一右端控制，取上确界即可。$\square$

**引理 10.6（CPTP 后处理的迹距离收缩）。** 若 $\Lambda:\mathcal L(X)\to\mathcal L(Y)$ 为 CPTP，则对任意 $\rho,\sigma\in\mathcal D(X)$，
$$
d_1(\Lambda(\rho),\Lambda(\sigma))\le d_1(\rho,\sigma).
\tag{10.11}
$$
这对任何有限维参考系统 $E$ 上的 $\Lambda\otimes\operatorname{id}_E$ 同样成立。

**证明。** 写 Hermitian 差的 Jordan 分解 $\rho-\sigma=H_+-H_-$，其中 $H_\pm\ge0$ 且
$$
\|\rho-\sigma\|_1=\operatorname{Tr}H_++\operatorname{Tr}H_-.
$$
由正性、保迹性和三角不等式，
$$
\|\Lambda(\rho-\sigma)\|_1
\le\|\Lambda(H_+)\|_1+\|\Lambda(H_-)\|_1
=\operatorname{Tr}H_++\operatorname{Tr}H_-.
$$
除以二得式(10.11)。完全正性保证 $\Lambda\otimes\operatorname{id}_E$ 为正，且该映射仍保迹，故同证适用。

这一证明使用的正负部分分解与本库 [FiniteTraceDistance](../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean) 的 **traceDistance_contract** 相同；后者的通道声明采用相同输入输出载体。本节允许不同有限维输入输出，并显式保留参考。一般迹范数收缩也见 John Watrous，[*The Theory of Quantum Information*](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，Corollary 3.40，式(3.241)。 $\square$

**命题 10.7（通道距离的参考量词）。** 对两个同型 CPTP 通道 $\Phi,\Psi:\mathcal L(X)\to\mathcal L(Y)$，定义
$$
d_\diamond(\Phi,\Psi)
=\sup_{\substack{E\text{ 有限维}\\
                  \eta_{XE}\in\mathcal D(X\otimes E)}}
d_1\!\left((\Phi\otimes\operatorname{id}_E)(\eta),
           (\Psi\otimes\operatorname{id}_E)(\eta)\right).
\tag{10.12}
$$
此量等于标准 diamond 范数距离 $\frac12\|\Phi-\Psi\|_\diamond$，且满足 $0\le d_\diamond\le1$。上确界可在 $\dim E=\dim X$ 的纯态输入上取到最大值。

式(10.12)沿用[量子上下文卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)第72、120节的完整通道比较：输入可以与保留参考纠缠，且两个通道接受同一个联合输入。参考不经被比较通道处理；若某个记忆寄存器在槽内参与相互作用，它属于该槽的输入输出对象。

**证明。** 通道差保持 Hermitian 性，因此标准 diamond 范数与式(10.12)的相等性由 Watrous 上引书 Theorem 3.51，式(3.291)给出。参考维数的约化还可直接从式(10.12)看出：对任意混合输入作纯态凸分解，迹范数凸性表明其值不超过分解中各纯态值的最大值；每个纯态在 $X:E$ 切分上的 Schmidt 秩至多为 $\dim X$。将其参考支撑等距嵌入一个 $\dim X$ 维的空间，不改变输出差的非零奇异值。反之该固定参考本就在允许上确界内；纯态集的紧性和迹范数连续性给出最大值。输出均为归一化态，故距离至多一。$\square$

**命题 10.8（共同 CPTP 上下文不放大通道误差）。** 对任意 CPTP 通道 $\Gamma:W\to X$、$\Lambda:Y\to Z$，
$$
d_\diamond(\Lambda\circ\Phi\circ\Gamma,\,
           \Lambda\circ\Psi\circ\Gamma)
\le d_\diamond(\Phi,\Psi).
\tag{10.13}
$$
对任意有限维旁观系统 $M$，
$$
d_\diamond(\Phi\otimes\operatorname{id}_M,\,
           \Psi\otimes\operatorname{id}_M)
=d_\diamond(\Phi,\Psi).
\tag{10.14}
$$
更一般地，若共同接线由 CPTP 映射
$$
\Gamma:W\to X\otimes M,\qquad
\Lambda:Y\otimes M\to Z
$$
给出，则
$$
d_\diamond\!\left(
\Lambda\circ(\Phi\otimes\operatorname{id}_M)\circ\Gamma,\,
\Lambda\circ(\Psi\otimes\operatorname{id}_M)\circ\Gamma
\right)
\le d_\diamond(\Phi,\Psi).
\tag{10.15}
$$

这是 Watrous 上引书 Proposition 3.48 与参考稳定性的应用，也是量子上下文卷第72节历史抬升误差界的单槽条件。前后处理必须在两个被比较对象间共用；若更换控制器或遗漏会参与后续操作的寄存器，就改变了式(10.15)的比较对象。

**证明。** 固定任意参考 $E$ 和联合输入 $\eta_{WE}$。$\Gamma\otimes\operatorname{id}_E$ 的输出仍是合法密度算子，因此中间通道差由式(10.12)控制；再用引理10.6处理 $\Lambda\otimes\operatorname{id}_E$，最后取上确界，得到式(10.13)。在式(10.14)左端，将 $M\otimes E$ 整体视为 $\Phi,\Psi$ 的参考，得“$\le$”；在右端任意测试输入上额外张量一个固定的 $M$ 态，迹范数因 $\|\tau_M\|_1=1$ 而不变，得“$\ge$”。式(10.15)由式(10.13)、(10.14)接续得到。$\square$

**命题 10.9（共用恢复器的两态下界）。** 设 $\mathcal E:X\to Y$ 为保留记录通道，$\mathcal T:X\to Z$ 为目标通道，$\mathcal R:Y\to Z$ 为任意共用 CPTP 恢复器。对任意 $\rho,\sigma\in\mathcal D(X)$，令
$$
e_\rho=d_1(\mathcal T(\rho),\mathcal R\mathcal E(\rho)),
\qquad
e_\sigma=d_1(\mathcal T(\sigma),\mathcal R\mathcal E(\sigma)).
$$
则
$$
\max\{e_\rho,e_\sigma\}
\ge\frac12\left[
d_1(\mathcal T(\rho),\mathcal T(\sigma))
-d_1(\mathcal E(\rho),\mathcal E(\sigma))
\right].
\tag{10.16}
$$

**证明。** 在两个目标态之间插入 $\mathcal R\mathcal E(\rho)$ 和 $\mathcal R\mathcal E(\sigma)$，两次三角不等式及引理10.6给出
$$
d_1(\mathcal T(\rho),\mathcal T(\sigma))
\le e_\rho+
d_1(\mathcal E(\rho),\mathcal E(\sigma))+e_\sigma.
$$
再用 $e_\rho+e_\sigma\le2\max\{e_\rho,e_\sigma\}$。

式(10.16)是量子上下文卷第120.4节相位态反例所用的两态论证；本库 [FiniteRecordRecoveryError](../../../D5/S3/Quantum/Decoherence/FiniteRecordRecoveryError.lean) 的 **finite_record_recovery_error_lower_bound** 将同一论证用于有限移位记录通道，得到 $(1-|\gamma|)/2$ 的恢复误差下界。 $\square$

**命题 10.10（逐态存在不允许交换量词：擦除反例）。** 令 $X=\mathbb C^2$、$Y=\mathbb C$，取擦除通道
$$
\mathcal E(H)=\operatorname{Tr}H,\qquad
\rho_0=|0\rangle\langle0|,\qquad
\rho_1=|1\rangle\langle1|.
$$
分别定义制备通道 $\mathcal R_i(z)=z\rho_i$。则
$$
\forall i\in\{0,1\}\ \exists\mathcal R_i,\quad
\mathcal R_i\mathcal E(\rho_i)=\rho_i,
$$
但任何共用恢复器 $\mathcal R$ 都满足
$$
\max_{i\in\{0,1\}}d_1(\rho_i,\mathcal R\mathcal E(\rho_i))
\ge\frac12.
\tag{10.17}
$$

**证明。** 两个擦除输出相同，而目标态距离为一，代入式(10.16)即可。制备 $\tau=I_X/2$ 时，两项距离均为 $1/2$，所以式(10.17)在这两个测试态组成的态族上最优。若固定 $\mathcal R_0$，则恢复在 $\rho_0$ 上误差为零，在 $\rho_1$ 上误差为一，从而
$$
d_\diamond(\operatorname{id}_X,\mathcal R_0\circ\mathcal E)=1.
\tag{10.18}
$$
下界由输入 $\rho_1$ 给出，上界由命题10.7给出。

把此例中的 $A,B$ 取为一维、$C=X$，每个 $\rho_i$ 的 $I(A:C\mid B)$ 都为零；但两个 $BC$ 边缘不同，所以它不满足定理10.4的共同边缘假设。式(10.18)同时表明，某个输入上的零恢复误差不能推出该恢复通道的 diamond 误差小。 $\square$

**推论 10.11（恢复误差对后续任务的有效范围）。** 在推论10.5的假设下，对每个 $\rho\in\mathcal F$，令 $\widehat\rho=(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})$。若 $\Lambda$ 是定义于完整 $ABC$ 输出上的共同 CPTP 后处理，则
$$
d_1(\Lambda(\rho),\Lambda(\widehat\rho))
\le\sqrt{1-e^{-\varepsilon}}.
\tag{10.19}
$$
特别地，对任意有限结果的共同 POVM 读出，其输出概率分布的总变差距离至多为此值；任意取值于 $[0,L]$ 的共同损失函数之期望差，绝对值至多为 $L\sqrt{1-e^{-\varepsilon}}$。

这一任务界控制所声明的固定边缘态族。定理10.4虽然量化所有有限维 $A$，仍要求每个联合输入的 $BC$ 边缘等于 $\omega_{BC}$；diamond 距离则对全部输入态取上确界。要得到
$$
d_\diamond(\operatorname{id}_{BC},
           \mathcal R_\omega\circ\operatorname{Tr}_C)\le\delta,
$$
必须另外证明同一个 $\mathcal R_\omega$ 对式(10.12)中的全部联合输入具有误差界 $\delta$。固定边缘上的估计不包含这个额外量词。相反，一旦 diamond 界成立，命题10.8就使它对所有共同 CPTP 接线成立。这与量子上下文卷第120—122节区分状态族缺陷、完整过程缺陷及共同模拟器的方式一致。

**证明。** 式(10.19)是式(10.10)与引理10.6的组合。POVM 是到经典对角态的 CPTP 通道，而对角态的半迹距离正好是总变差距离。若输出分布为 $p,q$，写 $\Delta=p-q$，则 $\sum\Delta=0$、正部分与负部分的总质量均为 $\operatorname{TV}(p,q)$。因此 $0\le\ell\le L$ 给
$$
\left|\sum_y\ell(y)(p(y)-q(y))\right|
\le L\,\operatorname{TV}(p,q).
$$
$\square$

## 10.99 追加锚

## 11. 带记忆量子过程的表示、历史概率与可访问关系

**定义 11.1（有限维载体与 Choi 约定）。** 全部 Hilbert 空间均为非零有限维复空间，$\mathcal L(A)$ 表示 $A$ 上的全部复线性算子。对每个输入空间 $A$ 固定正交归一基 $\{|i\rangle\}_{i=1}^{d_A}$，把输入参考副本 $A'$ 与 $A$ 按此基识别，并记
$$
E_{ij}=|i\rangle\langle j|,\qquad
|\Omega_A\rangle=\sum_{i=1}^{d_A}|i\rangle_{A'}\otimes|i\rangle_A.
\tag{11.1}
$$
对复线性映射 $\Phi:\mathcal L(A)\to\mathcal L(B)$，取输入参考在前、输出在后的未归一化 Choi 算子
$$
J(\Phi)
=(\operatorname{id}_{A'}\otimes\Phi)(|\Omega_A\rangle\langle\Omega_A|)
=\sum_{i,j}E_{ij}^{A'}\otimes\Phi(E_{ij})
\in\mathcal L(A'\otimes B).
\tag{11.2}
$$
符号 $\mathsf T$ 表示所选基中的普通转置，$\dagger$ 表示共轭转置；基底运输同时运输转置约定。无歧义时将 $A'$ 简写为 $A$。完全正量化所有有限参考 $R$ 上 $\operatorname{id}_R\otimes\Phi$ 的正性；不增迹指对每个 $X\ge0$ 有 $\operatorname{Tr}\Phi(X)\le\operatorname{Tr}X$。

**定理 11.2（Choi 重建与完全正、迹条件）。** 定义11.1给出全部复线性映射与 $\mathcal L(A'\otimes B)$ 之间的线性双射，逆映射为
$$
\Phi(X)=\operatorname{Tr}_{A'}\bigl[(X^{\mathsf T}\otimes I_B)J(\Phi)\bigr].
\tag{11.3}
$$
且
$$
\begin{aligned}
\Phi\text{ 完全正}&\iff J(\Phi)\ge0,\\
\Phi\text{ 保迹}&\iff \operatorname{Tr}_B J(\Phi)=I_{A'},\\
\Phi\text{ 完全正且不增迹}
&\iff J(\Phi)\ge0\ \text{且}\ \operatorname{Tr}_B J(\Phi)\le I_{A'}.
\end{aligned}
\tag{11.4}
$$

**证明。** 因为 $\operatorname{Tr}(X^{\mathsf T}E_{ij})=X_{ij}$，式(11.3)返回 $\sum_{ij}X_{ij}\Phi(E_{ij})$。反过来，任意 $J$ 的 $(i,j)$ 输入块唯一指定 $\Phi(E_{ij})$；矩阵单位是一组复基，因此得到双射。

若 $\Phi$ 完全正，式(11.2)是正算子在正性放大下的像。若 $J(\Phi)\ge0$，取有限谱分解
$$
J(\Phi)=\sum_\alpha|v_\alpha\rangle\langle v_\alpha|,
\qquad v_\alpha=\sum_i|i\rangle\otimes K_\alpha|i\rangle,
\tag{11.5}
$$
其中特征值平方根吸入 $v_\alpha$，$K_\alpha:A\to B$ 由其列确定。逐输入块比较得
$$
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
\tag{11.6}
$$
任意参考上的放大为 $\sum_\alpha(I_R\otimes K_\alpha)X(I_R\otimes K_\alpha)^\dagger$，故保持正性。零 Choi 算子取空和。

$\operatorname{Tr}_BJ(\Phi)$ 的 $(i,j)$ 元为 $\operatorname{Tr}\Phi(E_{ij})$，所以它等于 $I$ 当且仅当 $\Phi$ 在全部矩阵单位、进而全部复矩阵上保迹。对完全正映射，令 $F=\sum_\alpha K_\alpha^\dagger K_\alpha\ge0$。迹循环给 $\operatorname{Tr}\Phi(X)=\operatorname{Tr}(FX)$，且 $\operatorname{Tr}_BJ(\Phi)=F^{\mathsf T}$。对全部 $X\ge0$ 不增迹等价于 $F\le I$：充分性用正算子的迹配对非负，必要性取 $X=|u\rangle\langle u|$。转置保持正序，得到式(11.4)。

这是 Choi—Kraus 定理的有限维形式，见 Watrous，*The Theory of Quantum Information*，2018，[第2章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，式(2.64)—(2.66)、定理2.22与2.26，印刷第78、82—84、87—89页。完整 Kraus 族的通道接口亦见 [FiniteKrausChannel](../../../D5/S3/Quantum/Foundation/FiniteKrausChannel.lean) 的 finite_kraus_quantum_channel。$\square$

**命题 11.3（因子次序与归一化运输）。** Watrous 的输出在前约定 $J_W(\Phi)\in\mathcal L(B\otimes A')$ 与式(11.2)由交换两因子的固定酉映射对应。通道满足 $\operatorname{Tr}J(\Phi)=d_A$。归一化 Bell 输入给出的 $\widehat J=J/d_A$ 满足
$$
\operatorname{Tr}\widehat J=1,\qquad
\operatorname{Tr}_B\widehat J=I_{A'}/d_A,
$$
且以 $\widehat J$ 重建时，式(11.3)右侧须乘 $d_A$。

**证明。** 对式(11.2)逐项交换张量因子即得文献约定。对式(11.4)的偏迹等式取总迹，得 $\operatorname{Tr}J=d_A$；其余由线性缩放得到。$\square$

**命题 11.4（顺序接线的 Choi 收缩）。** 若 $\Phi:\mathcal L(A)\to\mathcal L(B)$、$\Psi:\mathcal L(B)\to\mathcal L(C)$，则在 $A\otimes B\otimes C$ 的次序下
$$
J(\Psi\circ\Phi)
=\operatorname{Tr}_B\!\left[
\bigl(J(\Phi)^{\mathsf T_B}\otimes I_C\bigr)
\bigl(I_A\otimes J(\Psi)\bigr)
\right].
\tag{11.7}
$$
这里 $\mathsf T_B$ 只转置接线空间 $B$；两个乘因子不要求交换。

**证明。** 展开 $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ 与 $J(\Psi)=\sum_{kl}E_{kl}\otimes\Psi(E_{kl})$，再用
$$
\operatorname{Tr}\bigl(\Phi(E_{ij})^{\mathsf T}E_{kl}\bigr)
=\Phi(E_{ij})_{kl},
$$
所得 $(i,j)$ 块正是 $\Psi(\Phi(E_{ij}))$。这是 Chiribella、D’Ariano、Perinotti，*Theoretical framework for quantum networks*，Physical Review A 80，022339（2009），[arXiv:0904.4483v2](https://arxiv.org/pdf/0904.4483v2)，定理1及式(13)，PDF第3页的 link product 在本节次序下的形式。中间乘积不必 Hermitian；复合完全正时最终 Choi 算子的正性由定理11.2保证。$\square$

**定义 11.5（因果梳与实际记忆接线）。** 固定 $n\ge1$。第 $k$ 轮先接收 $A_k$、再输出 $B_k$，之后才进入第 $k+1$ 轮；实验者可以根据先前输出及其保留记忆制备后续输入。令
$$
\mathcal H_k=A_1'\otimes B_1\otimes\cdots\otimes A_k'\otimes B_k,
\qquad\mathcal H_0=\mathbb C.
\tag{11.8}
$$
确定性因果梳由正算子 $R^{(k)}\in\mathcal L(\mathcal H_k)$ 给出，满足
$$
R^{(0)}=1,\qquad
\operatorname{Tr}_{B_k}R^{(k)}=R^{(k-1)}\otimes I_{A_k'}
\quad(1\le k\le n).
\tag{11.9}
$$
右侧次序为 $\mathcal H_{k-1}\otimes A_k'$。从末时刻向前排列时，同一条件写为 $I_{A_k'}\otimes R^{(k-1)}$，两种写法以固定因子置换对应。

顺序网络的 Choi 算子指：将网络视作从 $\bigotimes_kA_k$ 到 $\bigotimes_kB_k$ 的多部件通道，按式(11.2)取 Choi 算子，再排成式(11.8)。实际环境若跨两步回流，就作为同一个内部记忆接线；用两个约化系统通道替代该接线，须另有约化闭合等式。因果梳的时域 $n$、内部记忆实现和实验者可接入的端口分别作为数据；固定有限时域的记忆实现不附带跨全部时域的统一维数合同。

**定理 11.6（有限时域梳的实现）。** 在定义11.5的有限维、固定时间次序下，正性与式(11.9)等价于存在有限维记忆 $M_k$、$M_0=\mathbb C$ 及等距映射
$$
V_k:M_{k-1}\otimes A_k\longrightarrow B_k\otimes M_k,
\qquad V_k^\dagger V_k=I,
\tag{11.10}
$$
使顺序网络在最后舍弃 $M_n$ 后给出 $R^{(n)}$。允许一般逐轮 CPTP 映射给出同一类梳。其迹满足
$$
\operatorname{Tr}R^{(k)}=\prod_{j=1}^k d_{A_j}.
\tag{11.11}
$$

**证明。** 充分性是 Chiribella、D’Ariano、Perinotti 所引版本定理3与定理5，PDF第7、11页：取文献的 $H_{2k-2}=A_k$、$H_{2k-1}=B_k$，再置换成式(11.8)。一般 CPTP 实现的逐轮 Stinespring 环境可并入后续记忆；混合初始记忆可在第一轮制备并净化。

对必要性，令 $\Gamma_k$ 为前 $k$ 轮后舍弃内部记忆的多部件通道。最后一次操作保迹，故对全部输入算子 $X$ 有
$$
\operatorname{Tr}_{B_k}\Gamma_k(X)
=\Gamma_{k-1}(\operatorname{Tr}_{A_k}X).
\tag{11.12}
$$
此前输出上隐含恒等映射。把 $X$ 展开成输入矩阵单位，$A_k$ 上的迹给 $\delta_{ij}$，正好得到式(11.9)。这也适用于跨时间输入相关的 $X$。反复取迹给式(11.11)。文献第7—8页以各前缀 Choi 秩构造等距实现的记忆维数上界；该上界描述一种实现，不等同于最小物理记忆或最小控制门数。$\square$

**命题 11.7（整体保迹不足以保证时间因果性）。** 存在多部件酉通道不满足定义11.5的指定时间次序。

**证明。** 取两个 qubit 输入，以交换通道把 $A_2$ 送至 $B_1$、$A_1$ 送至 $B_2$。它完全正且保迹。固定 $A_1$，分别输入 $A_2=|0\rangle$ 或 $|1\rangle$，第一轮输出 $B_1$ 随第二轮输入改变，违反式(11.12)，故不满足式(11.9)。$\square$

**定义 11.8（过程张量与梳的端口对应）。** 固定时刻 $0,\ldots,k$、系统端口 $S_j^{\mathrm{in}}$ 和 $S_j^{\mathrm{out}}$。控制分支为完全正不增迹映射 $\mathcal A_j:\mathcal L(S_j^{\mathrm{in}})\to\mathcal L(S_j^{\mathrm{out}})$；确定性控制为 CPTP。给共同初态 $\rho_{S_0E}$，其中 $S_0=S_0^{\mathrm{in}}$，及同型接续的 CPTP 映射 $\mathcal U_{j+1:j}:\mathcal L(S_j^{\mathrm{out}}\otimes E)\to\mathcal L(S_{j+1}^{\mathrm{in}}\otimes E)$，定义
$$
\mathfrak T_{k:0}[\mathcal A_{k-1},\ldots,\mathcal A_0]
=\operatorname{Tr}_E\!\left[
\mathcal U_{k:k-1}(\mathcal A_{k-1}\otimes\operatorname{id}_E)
\cdots\mathcal U_{1:0}(\mathcal A_0\otimes\operatorname{id}_E)
(\rho_{S_0E})\right].
\tag{11.13}
$$
其值为未归一化终态，迹为所选结果序列的概率。独立控制时它对各 $\mathcal A_j$ 分别线性，进而在线性张量积上延伸；反馈或反复接触同一个控制辅助系统时，控制对象取具有对应时间次序的联合控制梳，保持同一辅助实现。

在各系统端口同维且联合演化为酉时，式(11.13)即为 Pollock、Rodríguez-Rosario、Frauenheim、Paternostro、Modi，*Non-Markovian quantum processes: complete framework and efficient characterisation*，[arXiv:1512.00589v3](https://arxiv.org/pdf/1512.00589v3)，定义1、性质P1—P3及定理2，PDF第2—3页的开放量子演化式(2)。其完全正性量化带控制辅助系统的物理输出，containment 按已声明的槽填充操作抽取子区间；在同型槽填入恒等控制与舍弃前段后重置环境是不同操作。该文图4（第5页）将过程及相关控制都表示为量子梳，定理4（第7页）给多时 Choi 表示，第IV.C节（第8页）给因果偏迹及子过程收缩。

本节按定义11.5表示同一端口结构：令 $n=k+1$、$A_1=\mathbb C$、$B_1=S_0^{\mathrm{in}}$，并对 $0\le j<k$ 取
$$
A_{j+2}=S_j^{\mathrm{out}},\qquad B_{j+2}=S_{j+1}^{\mathrm{in}}.
\tag{11.14}
$$
因此过程首先输出初始系统，随后每次接收控制后的系统并给出下一系统；控制 $\mathcal A_j$ 接在 $B_{j+1}$ 与 $A_{j+2}$ 之间。未归一化 Choi 梳具有正性与式(11.9)的因果偏迹条件，$R^{(1)}=\rho_{S_0}$；其实现取定理11.6。若以迹一多时 Choi 密度表示，则除以 $\prod_{j=0}^{k-1}\dim S_j^{\mathrm{out}}$，相应收缩公式同时运输此因子。端口量化、归一化与允许控制族属于同一表示合同。

**定义 11.9（历史索引仪器）。** 使用[量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)第72节的完整历史、活动记忆与惰性参考规范。固定时域 $N$、非空有限结果集 $Y_t$ 和每层共同有限维载体 $Q_t$。$Q_t=S_t\otimes M_t$ 包含系统与仍会回流的物理记忆。不同历史的载体通过已声明的共同嵌入识别；动作和仪器的类型在同层一致。

对已取得历史 $h=(y_1,\ldots,y_{t-1})$，控制器选择 $a=\pi_t(h)$，并指定
$$
\Phi^{h,a}_{t,y}:\mathcal L(Q_{t-1})\to\mathcal L(Q_t)
\quad(y\in Y_t),\qquad
\Phi^{h,a}_{t,y}\text{ 完全正},\qquad
\sum_y\Phi^{h,a}_{t,y}\text{ 保迹}.
\tag{11.15}
$$
在所比较输入族的每个可达正概率历史上动作须合法；或以失败结果给出总化仪器。全族都不可达的历史可作同型合法扩展，但扩展对各输入共同固定。随机控制的实际随机变量及复用位置并入历史或载体。

给任意有限惰性参考 $R$ 及共同初态密度 $\rho_{RQ_0}$，定义
$$
\sigma_\varnothing=\rho_{RQ_0},\qquad
\sigma_{hy}=(\operatorname{id}_R\otimes\Phi^{h,\pi_t(h)}_{t,y})(\sigma_h),
\qquad p(h)=\operatorname{Tr}\sigma_h,
\tag{11.16}
$$
并令 $\Phi_h$ 为沿 $h$ 按时间从右向左的分支复合，$\Phi_\varnothing=\operatorname{id}$。全过程使用同一初态及物理记忆，不要求 $R$ 与 $Q_0$ 独立。仪器的完全正分支及经典旗标约定亦见 Watrous 所引第2章第2.3.2节、式(2.255)—(2.262)，印刷第111—113页。

**定理 11.10（历史树归一化与历史 POVM）。** 定义11.9给出非负联合概率，满足
$$
\sum_{y\in Y_t}p(hy)=p(h),\qquad
\sum_{h\in Y_1\times\cdots\times Y_t}p(h)=1.
\tag{11.17}
$$
对任意前缀 $h$，全部有限后续结果求和仍为 $p(h)$。每层的 $\sum_{|h|=t}\Phi_h$ 是 CPTP，并且
$$
\sigma_h=(\operatorname{id}_R\otimes\Phi_h)(\rho_{RQ_0}),\qquad
E_h=\Phi_h^*(I_{Q_t})\ge0,\qquad
\sum_{|h|=t}E_h=I_{Q_0},\qquad
p(h)=\operatorname{Tr}(E_h\rho_{Q_0}),
\tag{11.18}
$$
其中 $\Phi_h^*$ 为 Hilbert–Schmidt 伴随。仅当 $p(h)>0$ 时定义条件态 $\sigma_h/p(h)$ 与下一结果概率 $p(hy)/p(h)$。正概率完整历史满足
$$
p(y_1,\ldots,y_t)=\prod_{j=1}^t p(y_j\mid y_1,\ldots,y_{j-1}).
\tag{11.19}
$$

**证明。** 完全正保证各 $\sigma_h\ge0$。固定父历史后，仪器之和保迹，故
$$
\sum_y\operatorname{Tr}\sigma_{hy}
=\operatorname{Tr}\left[(\operatorname{id}_R\otimes\sum_y\Phi^{h,\pi_t(h)}_{t,y})(\sigma_h)\right]
=\operatorname{Tr}\sigma_h.
$$
从 $p(\varnothing)=1$ 按层归纳得归一化，从末层向前求和得前缀一致性。正算子迹零必为零，故零概率父支的全部后继也为零。

每个 $\Phi_h$ 完全正。同一历史树逐层求和保迹，故其层和是通道；完全正伴随及其保单位性给式(11.18)。最后一个迹恒等式由 Hilbert–Schmidt 伴随的定义及参考系统偏迹直接得到。同一输入输出载体时，亦可应用 [FiniteKrausInstrumentBornMarginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean) 的 finite_kraus_instrument_born_marginal；本节允许不同 $Q_0,Q_t$ 的情形由上述直接计算承担。式(11.19)由各相邻比值望远镜相乘得到。条件概率依赖同一前缀的条件态与动作，不能由该式换为无条件边缘的乘积。$\square$

**定义 11.11（经典档案、活动记忆与参考）。** 历史档案 $H_t$ 具有正交基 $\{|h\rangle\}_{|h|=t}$，对应联合记录为
$$
\Omega_t=\sum_{|h|=t}|h\rangle\langle h|_{H_t}\otimes\sigma_h
\in\mathcal L(H_t\otimes R\otimes Q_t).
\tag{11.20}
$$
经典性指定 $H_t$ 基中的块对角结构；各 $RQ_t$ 块仍保留其量子关联。活动记忆 $M_t$ 指已声明分解 $Q_t=S_t\otimes M_t$ 中后续可相互作用的因子，其控制权限、重置及回流均属于操作合同。惰性参考 $R$ 指过程中始终不被操作的关联因子；若后来与系统相互作用，该因子转入活动载体或开放端口。档案可读字段及可复制标签、物理记忆可控制操作、参考的可制备与终端可读取范围分别指定。

**命题 11.12（记录归一化、压缩与反馈取值）。** 式(11.20)为密度矩阵；舍弃档案给 $\sum_h\sigma_h$。对经典函数 $q:H_t\to Z$，压缩给
$$
\Omega_t^q=\sum_z|z\rangle\langle z|\otimes\sum_{q(h)=z}\sigma_h.
\tag{11.21}
$$
仅以 $z=q(h)$ 选择与原策略相同的确定性动作，当且仅当 $\pi$ 在 $q$ 的每个相关纤维上常值。

**证明。** 每块正且块迹之和由式(11.17)为一。偏迹与经典推前逐块计算即得两种输出。若 $\pi=\bar\pi\circ q$，同纤维的动作相同；反之，在每个非空相关纤维取该共同动作便定义 $\bar\pi$。这项等价只约束依赖档案的动作函数；若允许从 $Q_t$ 另读信息，须验证该额外读出及其扰动是否实现相同协议。受控充分状态与统一过程模拟的相应条件见量子卷第118.16、120节。$\square$

**命题 11.13（有限载体与条件状态个数）。** 固定时域 $t$ 的档案基大小为 $\prod_{j=1}^t|Y_j|$；固定有限维物理载体的跨时域可达密度集合却可以无限。

**证明。** 前一式为有限笛卡尔积计数。后一式取单结果 qubit 仪器 $\rho\mapsto U\rho U^\dagger$，其中 $U=\operatorname{diag}(1,e^{i\theta})$、$\theta/(2\pi)$ 无理，初态为 $|+\rangle\langle+|$。第 $t$ 步非对角元为 $e^{-it\theta}/2$，不同 $t\ge0$ 给不同密度。于是载体维数二并不给有限个可达条件态。量子卷第151节的有限经典隐状态实现另以保留全部旗标的逐块纠缠破坏为前提，且限定中途干预及端点输出；本例不取消或代替这些条件。$\square$

**命题 11.14（相同局部态与记录访问的区别）。** 取 qubit $S,M$，令
$$
|\pm\rangle=\frac{|0\rangle\pm|1\rangle}{\sqrt2},\qquad
|\Phi_\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
\tag{11.22}
$$
两联合纯态正交，双方局部态均为 $I_2/2$。未来若仅操作 $S$ 及独立于 $SM$、且制备不依赖符号的辅助系统，$M$ 始终不回流，则全部这类仪器历史统计相同。若允许控制 $SM$ 上的耦合 $U|i,j\rangle=|i,j\mathbin{\mathrm{XOR}}i\rangle$，则逆耦合后测量 $S$ 的 $X$ 基能完全区分两态。若实际测量 $M$ 的计算基并只保存经典结果及 $S$，两个输出反而相同。

**证明。** 取 $\rho=|+\rangle\langle+|$、$\sigma=|-\rangle\langle-|$，它们对角元相同且非对角元不同。[CanonicalRecordAccessRecovery](../../../D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.lean) 的 reduced_irreversibility_is_canonical_record_access_defect 直接给 copied-address 模型的全局区别、约化同一、无共同约化恢复函数及实际记录的逆耦合恢复。此例中
$$
U(|\pm\rangle_S|0\rangle_M)=|\Phi_\pm\rangle,
\qquad U^\dagger|\Phi_\pm\rangle=|\pm\rangle_S|0\rangle_M.
\tag{11.23}
$$
局部偏迹各为 $I_2/2$，故限定局部协议从同一局部态出发，定理11.10给相同历史权重。允许 $U^\dagger=U$ 时，后续 $\{|+\rangle\langle+|,|-\rangle\langle-|\}$ 测量分别给确定结果。计算基测量 $M$ 后的经典记录与条件 $S$ 态对两个符号均为
$$
\frac12|0\rangle\langle0|_H\otimes|0\rangle\langle0|_S
+\frac12|1\rangle\langle1|_H\otimes|1\rangle\langle1|_S.
\tag{11.24}
$$
该相同输出的任何共同后处理仍相同，故保存标签本身不恢复相位。$\square$

**定理 11.15（精确不可克隆与经典档案的恢复界限）。** 设单位向量 $\psi,\phi\in H$ 满足 $0<|\langle\psi,\phi\rangle|<1$，记 $P_\psi=|\psi\rangle\langle\psi|$。不存在同一个 CPTP 映射 $\mathcal C:\mathcal L(H)\to\mathcal L(H\otimes H)$ 同时满足
$$
\mathcal C(P_\psi)=P_\psi\otimes P_\psi,\qquad
\mathcal C(P_\phi)=P_\phi\otimes P_\phi.
\tag{11.25}
$$
因此，对任何包含这两个态的输入族，不存在取值于有限经典寄存器的 CPTP 编码 $\mathcal E$ 及共同 CPTP 解码 $\mathcal R$，使 $\mathcal R\mathcal E$ 在该族上精确恢复原态。此结论的量词是同一确定性编码、解码对一个未知输入样本的精确全态恢复。

**证明。** 从式(11.6)及 $\sum_\alpha K_\alpha^\dagger K_\alpha=I$ 构造有限 Stinespring 等距映射 $Vx=\sum_\alpha K_\alpha x\otimes|\alpha\rangle_E$。若 $\mathcal C(P_\psi)=P_\psi\otimes P_\psi$，输出的纯性使
$$
V\psi=\psi\otimes\psi\otimes e_\psi
$$
对某个单位环境向量成立：投影至 $\psi\otimes\psi$ 正交补后的范数平方，等于该输出边缘在正交补上的迹，因而为零。同理 $V\phi=\phi\otimes\phi\otimes e_\phi$。等距性给
$$
|\langle\psi,\phi\rangle|
=|\langle\psi,\phi\rangle|^2|\langle e_\psi,e_\phi\rangle|
\le |\langle\psi,\phi\rangle|^2,
$$
与严格介于零和一矛盾。在没有剩余环境、指定共同空白及精确向量等式的等距模型中，这正是 [NoCloningInnerProductCriterion](../../../D5/S3/Quantum/PureState/NoCloningInnerProductCriterion.lean) 的 no_cloning_inner_product_criterion；量子卷第90.2节保留了该模型的假设。

再设经典编码与解码存在。对每个输入纯态，写 $\mathcal E(P_\psi)=\sum_zp_\psi(z)|z\rangle\langle z|$，$\tau_z=\mathcal R(|z\rangle\langle z|)$。若 $\sum_zp_\psi(z)\tau_z=P_\psi$，在 $\psi$ 的正交补上取迹，由每项非负可知所有 $p_\psi(z)>0$ 的 $\tau_z$ 均等于 $P_\psi$。经典复制通道 $\Delta(|z\rangle\langle z|)=|z,z\rangle\langle z,z|$ 因而使
$$
(\mathcal R\otimes\mathcal R)\Delta\mathcal E(P_\psi)
=\sum_zp_\psi(z)\tau_z\otimes\tau_z=P_\psi\otimes P_\psi.
$$
同一通道也复制 $P_\phi$，与前半部矛盾。正交标签的复制不满足 $0<|\langle\psi,\phi\rangle|<1$，故不受该禁制；带误差恢复或仅恢复指定任务也不满足式(11.25)的精确全态假设。$\square$

**定义 11.16（允许 tester 与过程距离）。** 对共同端口的确定性梳，固定一族实际允许的顺序 tester $\mathfrak T$，每个 tester 包含准备、槽间控制、其活动记忆与终端读出，并给有限经典输出分布 $p_T^R$。定义
$$
d_{\mathfrak T}(R,S)=\sup_{T\in\mathfrak T}\operatorname{TV}(p_T^R,p_T^S),
\tag{11.26}
$$
空族取零。tester 的正性、归一化与顺序实现采用 Chiribella等所引版本定义11及定理11，PDF第17页。实际允许族另受本卷共同实验语言、来源与费用合同约束。

**命题 11.17（共同 tester 距离的范围）。** $d_{\mathfrak T}$ 是值域 $[0,1]$ 的伪度量，其零核恰为所有 $T\in\mathfrak T$ 下输出分布相同的关系。固定接线和反馈得到的普通通道可使用第10节的 diamond 接口；若测试族允许槽间变化，则固定接线只贡献式(11.26)上确界中的一个子族。

**证明。** 每个总变差距离非负、对称且不超过一。逐 tester 的三角不等式取上确界仍给三角不等式；上确界为零当且仅当各项为零。固定共同控制并把活动记忆及历史保留在轮次类型中，CPTP 映射的有限复合仍为通道；扩大 tester 族只增大上确界。这是本卷既有固定读数族上确界构造的实例，量子卷第120.3节的固定接线与 comb 区别采用同一量词。$\square$

**定义 11.18（历史误差与资源接口）。** 对定义11.9的两个候选实现，完整轮次比较采用量子卷第72节的历史旗标通道，其输出包含 $H_t,Q_t$，并按第10节保留同一参考；式(11.16)的未归一化分支为其历史块。第12节的误差预算以这些共同类型、共同控制器及实际可达输入为合同。仅比较归一化后态的证书须另带正概率条件及分支权重；仅比较非选择和的证书不充作完整带旗标证书。

过程矩阵的数学给定、由有限实验估计该矩阵、实现其内部记忆及执行所选 tester 分别指定误差和费用。操作费用取本卷第7节的实际允许路径合同；Choi 或梳的存在表示本身不将准备、复制、记忆访问及读取操作加入允许语言。

## 11.99 追加锚

## 12. 可组合恢复、连续缺陷与相对时钟

**定义 12.1（同一任务的通道接口）。** 设 $X,B,A$ 为有限维复 Hilbert 空间，所有通道均完全正且保迹。固定边界编码 $\mathcal E:X\to B$、目标读出 $\mathcal Q:X\to A$、边界解码 $\mathcal S:B\to A$，以及完整操作 $\mathcal T_j:X\to X$ 和边界操作 $\overline{\mathcal T}_j:B\to B$。这里箭头表示相应矩阵代数间的通道。采用第10节包含外部参考的半 diamond 距离，记
$$
\kappa=d_\diamond(\mathcal S\mathcal E,\mathcal Q),\qquad
\varepsilon_j=d_\diamond(\mathcal E\mathcal T_j,
\overline{\mathcal T}_j\mathcal E).
\tag{12.1}
$$
这些是对同一通道族的统一界，不是对每个输入分别选择解码器后取得的最小值。取 $A=X,\mathcal Q=\operatorname{id}_X,\mathcal S=\mathcal R$，得到恢复完整输入的特例；一般 $\mathcal Q$ 则只指定任务需要的输出。空间类型包含会在后续再次操作的记录和物理记忆；始终不被操作的外部系统才作为惰性参考。

本卷第6节已经给出局部缺陷的路径传播，[量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) §72给出保留完整历史和活动记忆的通道望远镜界，§52给出无外部参考的末端预测界。以下将统一解码误差接到该既有传播结构，不把一般望远镜法视作新的原理。完全有界迹范数的成熟性质见 Watrous，[*The Theory of Quantum Information*](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§3.3，Proposition 3.48及式（3.306）。

**定理 12.2（恢复误差与关系运输误差的共同预算）。** 在定义12.1下，对每个 $n\ge0$，有
$$
\boxed{
d_\diamond\!\left(
\mathcal S\overline{\mathcal T}_n\cdots
\overline{\mathcal T}_1\mathcal E,
\mathcal Q\mathcal T_n\cdots\mathcal T_1
\right)
\le\min\left\{1,\kappa+\sum_{j=1}^n\varepsilon_j\right\}.}
\tag{12.2}
$$
因而接上同一个任意合法终端测量，全部输出分布的总变差也受此界控制。有限经典随机核采用 $d_{\rm cl}(P,Q)=\max_x\operatorname{TV}(P(\cdot\mid x),Q(\cdot\mid x))$ 时，同一式（12.2）成立。完整恢复特例就是
$$
d_\diamond(\mathcal R\overline{\mathcal T}_n\cdots
\overline{\mathcal T}_1\mathcal E,
\mathcal T_n\cdots\mathcal T_1)
\le\min\{1,\kappa+\textstyle\sum_j\varepsilon_j\}.
\tag{12.3}
$$
同一结论允许轮次类型改变：给 $\mathcal E_j:X_j\to B_j$、$\mathcal T_j:X_{j-1}\to X_j$、$\overline{\mathcal T}_j:B_{j-1}\to B_j$、$\mathcal Q_n:X_n\to A$ 与 $\mathcal S_n:B_n\to A$，取
$$
\kappa_n=d_\diamond(\mathcal S_n\mathcal E_n,\mathcal Q_n),\qquad
\varepsilon_j=d_\diamond(\mathcal E_j\mathcal T_j,
\overline{\mathcal T}_j\mathcal E_{j-1}).
$$
则
$$
d_\diamond(\mathcal S_n\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E_0,
\mathcal Q_n\mathcal T_n\cdots\mathcal T_1)
\le\min\{1,\kappa_n+\textstyle\sum_j\varepsilon_j\}.
\tag{12.3a}
$$

**证明。** 置 $D_j=\mathcal E\mathcal T_j-
\overline{\mathcal T}_j\mathcal E$。直接插入中间项得
$$
\mathcal E\mathcal T_n\cdots\mathcal T_1-
\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E
=\sum_{j=1}^n
\overline{\mathcal T}_n\cdots\overline{\mathcal T}_{j+1}
D_j\mathcal T_{j-1}\cdots\mathcal T_1.
\tag{12.4}
$$
空乘积取恒等通道。每项前后均为通道，其 diamond 范数为一，故半范数至多 $\varepsilon_j$。左接 $\mathcal S$ 不放大差；再插入 $\mathcal S\mathcal E\mathcal T_n\cdots\mathcal T_1$，余项为 $(\mathcal S\mathcal E-\mathcal Q)\mathcal T_n\cdots\mathcal T_1$，半范数至多 $\kappa$。三角不等式和两个通道距离不超过一给式（12.2）。同一测量仍是通道，故输出距离不增，经典对角态的迹距离等于总变差。变类型情形把第 $j$ 项的 $D_j$ 换为 $\mathcal E_j\mathcal T_j-\overline{\mathcal T}_j\mathcal E_{j-1}$，内部编码仍逐项抵消，末端改插入 $\mathcal S_n\mathcal E_n\mathcal T_n\cdots\mathcal T_1$，证明完全同样。经典版本直接用随机核的总变差收缩：对任意共同输入分布，两核输出差的总变差至多各点输入差的最大值；前接随机核为凸组合，后接随机核收缩。对同一望远镜恒等式逐项应用即可。$\square$

**命题 12.3（任务恢复与全部量子状态恢复的维数边界）。** 若定义12.1的完整恢复满足 $\mathcal R\mathcal E=\operatorname{id}_X$，则 $\dim B\ge\dim X$。任务恢复 $\mathcal S\mathcal E=\mathcal Q$ 不具有这一普遍下界。例如 $\mathcal Q$ 是只输出一个固定态的通道时，一维边界已经充分。

**证明。** $\mathcal E$ 具有线性左逆，因此在复向量空间 $\mathcal L(X)$ 上单射。于是 $(\dim X)^2\le(\dim B)^2$。固定态目标经一维迹通道再制备该固定态即得。故要求保留指定任务，与要求可逆编码所有未知量子状态具有不同量词。$\square$

**定义 12.4（受限输入与自适应续接）。** 若只在输入族或码空间上使用恢复保证，指定每个时刻允许的、可带参考的联合态集合 $\mathscr A_j$。要求理想前缀把 $\mathscr A_0$ 送入 $\mathscr A_j$；第 $j$ 步缺陷在 $\mathscr A_{j-1}$ 上统一成立，末端恢复缺陷在 $\mathscr A_n$ 上成立。各误差界必须采用同一解码、同一控制器与同一参考约定。对有限自适应协议，历史、控制器和活动量子记忆纳入各轮次类型；追加历史导致类型改变时，每轮编码及解码须有相应类型，不能把这些轮次写成一个固定空间上的幂。

量子卷§72.1、§72.3的完整轮次模型已经承担自适应误差传播：若控制器相同且每一步先将历史去相干，输入在历史寄存器上为块对角，则统一的逐历史分支界可经块权重求和用于整步。若控制器不同，其差异进入对应轮次缺陷；若历史相干，逐经典分支最大值不是完整通道界。这里的受限族定义不赋予未声明的复制或记录访问权限。

**命题 12.5（受限证书的传播及失效见证）。** 在定义12.4的受限族条件下，若 $\kappa,\varepsilon_j$ 是相应受限态上的统一预算，则对每个允许参考 $R$ 及 $\rho_{XR}\in\mathscr A_0$，
$$
\frac12\left\|\bigl[(\mathcal S\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E-\mathcal Q\mathcal T_n\cdots\mathcal T_1)\otimes\operatorname{id}_R\bigr](\rho_{XR})\right\|_1
\le\min\{1,\kappa+\textstyle\sum_j\varepsilon_j\}.
$$
该式按定义12.1写成固定类型；逐轮采用式（12.3a）的类型和相应受限输入族时，同一证明给变类型版本。这只是受限态保证，不断言全空间 diamond 缺陷同样小。如果缺少沿理想前缀的不变范围，结论不成立。对成功条件化的实验，未经归一化的通道误差也不直接给同值的条件误差。

**证明。** 对给定联合态使用式（12.4）；第 $j$ 项右侧的理想前缀将它送入 $\mathscr A_{j-1}$，故该项可使用受限缺陷。左侧的其余通道仍收缩迹距离；末端恢复项使用 $\mathscr A_n$ 上的界。求和得结论。

为说明范围必要性，取经典两态 $X=\{0,1\}$，边界为单点，$\mathcal E$ 擦除，$\mathcal R$ 总制备零，$\mathcal T$ 交换两态，边界更新恒等。初态族仅为零态；其恢复缺陷为零，编码交织缺陷处处为零。然而一步后理想态为一、恢复态为零，总变差为一。原因是末端已经离开恢复有效域。

条件化方面，设成功子态为 $A,B\succeq0$，$p=\operatorname{Tr}A>0,q=\operatorname{Tr}B>0$，且 $\|A-B\|_1\le e$。由 $|p-q|\le e$，
$$
\left\|\frac A p-\frac B q\right\|_1
\le\frac{\|A-B\|_1}{p}+\frac{|p-q|}{p}
\le\frac{2e}{p}.
\tag{12.5}
$$
故成功概率的共同下界 $p,q\ge s>0$ 给条件态迹距离至多 $\min\{1,e/s\}$。下界不能删除：两个经典联合输出分别以概率 $s$ 成功并输出相反比特，以概率 $1-s$ 给同一失败标签；完整输出总变差为 $s\to0$，成功条件分布的总变差却恒为一。失败旗标保留时仍可使用原通道界。$\square$

**定理 12.6（连续时间的交织缺陷）。** 在有限维空间中，设 $\mathcal T_t=e^{t\mathcal L}$、$\overline{\mathcal T}_t=e^{t\overline{\mathcal L}}$ 对全部 $t\ge0$ 均为通道。定义
$$
\mathcal K=\mathcal E\mathcal L-\overline{\mathcal L}\mathcal E,
\qquad \delta=\tfrac12\|\mathcal K\|_\diamond.
\tag{12.6}
$$
则
$$
\mathcal E\mathcal T_t-\overline{\mathcal T}_t\mathcal E
=\int_0^t\overline{\mathcal T}_{t-s}\mathcal K\mathcal T_s\,ds,
\tag{12.7}
$$
$$
d_\diamond(\mathcal E\mathcal T_t,\overline{\mathcal T}_t\mathcal E)
\le\min\{1,t\delta\},\qquad
d_\diamond(\mathcal S\overline{\mathcal T}_t\mathcal E,
\mathcal Q\mathcal T_t)\le\min\{1,\kappa+t\delta\}.
\tag{12.8}
$$
更一般地，连续时变生成元具有通道传播子 $\mathcal T(t,s)$、$\overline{\mathcal T}(t,s)$，且固定 $\mathcal E$ 满足 $\mathcal K(s)=\mathcal E\mathcal L(s)-\overline{\mathcal L}(s)\mathcal E$，则上述 $t\delta$ 替换为 $\int_{t_0}^{t_1}\tfrac12\|\mathcal K(s)\|_\diamond ds$。

**证明。** 对 $F(s)=e^{(t-s)\overline{\mathcal L}}\mathcal E e^{s\mathcal L}$ 求导，有限维乘积法则给 $F'(s)=\overline{\mathcal T}_{t-s}\mathcal K\mathcal T_s$。积分后两端分别为 $\mathcal E\mathcal T_t$ 与 $\overline{\mathcal T}_t\mathcal E$。范数积分不等式及通道范数一给首个界，插入 $\mathcal S\mathcal E\mathcal T_t$ 给恢复界。

时变情形对 $F(s)=\overline{\mathcal T}(t_1,s)\mathcal E\mathcal T(s,t_0)$ 使用传播子的前向、后向微分方程，得到相同积分恒等式。这里没有把非交换时变生成元的传播子替换成一般错误的 $e^{\int\mathcal L(s)ds}$。这是有限维变常数公式在交织缺陷上的应用；离散对应式已见[形式观察者卷](FORMAL_OBSERVER_COMPLETION_REFLECTION.md)定理17.1。$\square$

**定理 12.7（时间标记与费用测度的一致运输）。** 对定理12.6的时变过程，令 $t=f(\tau)$ 是区间上的 $C^1$ 严格递增换元，$f'(\tau)>0$。运输后的传播子为
$$
\mathcal T^f(\tau_1,\tau_0)
=\mathcal T(f(\tau_1),f(\tau_0)),
$$
边界传播子同理；相应生成元为 $\mathcal L^f(\tau)=f'(\tau)\mathcal L(f(\tau))$ 与 $\overline{\mathcal L}^f(\tau)=f'(\tau)\overline{\mathcal L}(f(\tau))$。于是
$$
\mathcal K^f(\tau)=f'(\tau)\mathcal K(f(\tau)),\qquad
\delta^f(\tau)=f'(\tau)\delta(f(\tau)),
\qquad
\int_{\tau_0}^{\tau_1}\delta^f(\tau)d\tau
=\int_{f(\tau_0)}^{f(\tau_1)}\delta(t)dt.
\tag{12.9}
$$
若某一非负费用坐标的累积量按 $\int c(t)dt+\sum_j b_j$ 定义，连续费率运输为 $c^f(\tau)=f'(\tau)c(f(\tau))$；时刻 $t_j$ 的点操作费用 $b_j$ 移至 $\tau_j=f^{-1}(t_j)$，其数值不变。相同区间的累计费用和累计缺陷均不变。这里每次实际记录的时刻 $t_j$ 仅重新标为 $f^{-1}(t_j)$，读数、条件化和控制协议保持同一物理实现；若改成在新钟上重新等步采样，通常改变了原物理样点，不能直接使用这条重参数化结论。

**证明。** 传播子的链式法则给生成元公式，固定 $\mathcal E$ 后交织缺陷同乘 $f'$。范数正齐次性给 $\delta^f$，积分换元给式（12.9）。连续费用用同一换元；有限点费用只是索引重排，故不乘 $f'$。可数可和的非负点费用也由单调极限得到同样结论。$\square$

**定义 12.8（允许的坐标运输及资源合同）。** 若 $F:X\to X'$、$G:B\to B'$、$H:A\to A'$ 是酉共轭通道，定义
$$
\mathcal E'=G\mathcal E F^{-1},\quad
\mathcal Q'=H\mathcal QF^{-1},\quad
\mathcal S'=H\mathcal SG^{-1},\quad
\mathcal T_j'=F\mathcal T_jF^{-1},\quad
\overline{\mathcal T}_j'=G\overline{\mathcal T}_jG^{-1}.
\tag{12.10}
$$
坐标运输本身不指称执行这些酉操作；若协议实际执行它们，执行费用另计。一个已准许路径的费用合同可以取任意有限维非负向量，逐坐标相加：编码、边界操作、解码分别有界为 $c_E,c_j,c_S$ 时，实现路径的费用不超过 $c_E+\sum_jc_j+c_S$。共同来源、同时取得的旁支、失败和复制许可仍按本卷第1、4、5、7节声明；误差上界不生成这些许可。

**命题 12.9（缺陷的合法运输与多层接口）。** 式（12.10）给
$$
\mathcal E'\mathcal T_j'-\overline{\mathcal T}_j'\mathcal E'
=G(\mathcal E\mathcal T_j-\overline{\mathcal T}_j\mathcal E)F^{-1},
\qquad
\mathcal S'\mathcal E'-\mathcal Q'=H(\mathcal S\mathcal E-\mathcal Q)F^{-1}.
\tag{12.11}
$$
所以 $\kappa,\varepsilon_j$ 保持不变。一般可逆线性变换仅给代数共轭恒等式，不保证通道合法性或范数保持。

若另外有第二层编码 $\mathcal E_2:B\to C$、解码 $\mathcal R_2:C\to B$ 和操作 $\widetilde{\mathcal T}_j$，令
$$
\kappa_2=d_\diamond(\mathcal R_2\mathcal E_2,\operatorname{id}_B),\qquad
\eta_j=d_\diamond(\mathcal E_2\overline{\mathcal T}_j,
\widetilde{\mathcal T}_j\mathcal E_2).
$$
复合编码 $\mathcal E_2\mathcal E$、解码 $\mathcal S\mathcal R_2$ 对同一目标 $\mathcal Q$ 的恢复缺陷至多 $\kappa+\kappa_2$，每步交织缺陷至多 $\varepsilon_j+\eta_j$。因此整段实验误差至多
$$
\min\{1,\kappa+\kappa_2+\textstyle\sum_j(\varepsilon_j+\eta_j)\}.
\tag{12.12}
$$

**证明。** 展开共轭并约去相邻逆映射得式（12.11）。酉通道及其逆均收缩 diamond 范数，两个方向的界给等号。第二层恢复差插入 $\mathcal S\mathcal E$；第二层交织差插入 $\mathcal E_2\overline{\mathcal T}_j\mathcal E$。三角不等式和通道收缩给两项缺陷预算，再应用定理12.2。这是本卷命题6.5在合法量子接口上的同一复合规则。$\square$

**定理 12.10（采样记忆接口接入稳定反馈的充分条件）。** 设 $U$ 为有限维实内积空间，$K,\widehat K:[0,\infty)\to\mathcal L(U)$ 可测且算子范数可积。令
$$
k=\int_0^\infty\|K(t)\|dt,\quad
\widehat k=\int_0^\infty\|\widehat K(t)\|dt,\quad
e_K=\int_0^\infty\|K(t)-\widehat K(t)\|dt.
$$
固定同一线性反馈 $A:U\to U$，$L=\|A\|$，并假设 $Lk<1,L\widehat k<1$。对有界可测 $f,\widehat f,g$，以下因果卷积方程在 $L^\infty([0,\infty);U)$ 中各有唯一解：
$$
x=f+K*(Ax+g),\qquad
\widehat x=\widehat f+\widehat K*(A\widehat x+g).
\tag{12.13}
$$
若 $\|f-\widehat f\|_\infty\le e_f$、$\|g\|_\infty\le G$，则
$$
\|x\|_\infty\le\frac{\|f\|_\infty+kG}{1-Lk},\qquad
\boxed{\|x-\widehat x\|_\infty
\le\frac{e_f+e_K(L\|x\|_\infty+G)}{1-L\widehat k}.}
\tag{12.14}
$$
恢复几何卷第11节的共同正谱隙模型给 $k\le m/a$、$\widehat k\le\widehat m/a$，其命题11.7给 $e_K\le\Phi_a(m+\widehat m,\varepsilon)$；第12节的积分误差比较的是两份前缀的规范模型；用于实际模型时，另须其命题12.6所列的实际—规范同一性或响应误差依据。例如实际—规范核的积分误差已有 $e_{\rm model}$ 上界时，可取 $e_K\le e_{\rm model}+2\sqrt R\,d_J/a+R d_A/a^2$，其中 Frobenius 界同时控制算子范数。满足这里的小增益条件后，这些边界采样证书便控制同一反馈中的完整响应。

**证明。** 令 $V_Kx=K*(Ax)$。积分三角不等式给 $\|V_K\|_{\infty\to\infty}\le kL<1$；因此 $\sum_{n\ge0}V_K^n$ 在算子范数中收敛，且为 $I-V_K$ 的逆。这是 Banach 空间上的 Neumann 级数。应用于 $f+K*g$ 得唯一性及第一个界；第二系统同理。

相减并使用同一个实际反馈 $A$，得
$$
\widehat x-x=(\widehat f-f)
+\widehat K*A(\widehat x-x)
+(\widehat K-K)*(Ax+g).
$$
取 $L^\infty$ 范数，把 $L\widehat k\|\widehat x-x\|_\infty$ 移到左边，得到式（12.14）。每个卷积及其幂均因果，级数极限也保留因果性。初态引起的外源项须归入 $f,\widehat f$ 并实际控制 $e_f$；核误差本身不给该控制。本结论针对式（12.13）及其小增益假设，不把核逼近自动提升为任意微分反馈方程的稳定性。$\square$

## 12.99 追加锚

## 13. 完整已获记录、因果割与边界运输

**定义 13.1（共同实现上的完整已获记录）。** 固定非空有限集合 $\Omega$，以及任意指标集 $A$ 上的一族已取得记录 $R_\alpha:\Omega\to\mathcal R_\alpha$。指标包含来源身份；内在记录、外部档案及已经取得的关系读数，凡在这个协议中表示者均列入此族。定义
$$
\omega\sim_C\omega'
\iff \forall\alpha\in A,\ R_\alpha(\omega)=R_\alpha(\omega'),
\qquad C:\Omega\to\mathcal C:=\Omega/{\sim_C}.
\tag{13.1}
$$
$C$ 称为本协议的完整已获记录接口。有限性来自 $\Omega$，不要求 $A$ 有限，也不把实际观察者等同于有限身体或一份预选短表。这里的商表示记录已经具有的区分；其构造不附带免费取得记录、免费计算商标签或有效解码的假设。

此处的共同实现与完整记录约定接续本卷第9节“经典概率拼接、记忆增益与可组合恢复”的同律条件，第10节“量子条件互信息、共用恢复与参考系统”的共同来源量词，第11节“带记忆量子过程的表示、历史概率与可访问关系”的档案与策略，以及第12节“可组合恢复、连续缺陷与相对时钟”的有类型续接。以下采用有限经典、不扰动的读数协议；不由此给量子仪器的不同控制分支指定未经假设的共同反事实取值。

**命题 13.2（完整记录商的精确性）。** 每个 $R_\alpha$ 唯一因子化为 $h_\alpha C$，且
$$
\sigma(C)=\sigma(R_\alpha:\alpha\in A).
\tag{13.2}
$$
若摘要 $M=m(C)$ 还满足每个 $R_\alpha$ 均通过 $M$ 因子化，则 $C$ 也通过 $M$ 因子化。因此，在没有另证所需充分性的情况下，用更粗的任务摘要替换 $C$ 会改变条件化所保留的信息。

**证明。** $R_\alpha$ 在每个 $C$ 类上常值，故在实际像上定义 $h_\alpha([\omega])=R_\alpha(\omega)$，良定义且唯一。这给 $\sigma(R_\alpha:\alpha\in A)\subseteq\sigma(C)$。固定 $\omega$；对每个不在其类中的 $\omega'$，选择一个区分二者的指标 $\alpha_{\omega'}$。这样的 $\omega'$ 只有有限个，相应等值事件的交恰为 $[\omega]$。无类外点时这个交为 $\Omega$。每个类均属于右侧的 $\sigma$ 代数，故反向包含成立。最后，若 $M(\omega)=M(\omega')$，全部 $R_\alpha$ 相同，所以 $C(\omega)=C(\omega')$；按 $M$ 的非空纤维定义因子即得结论。$\square$

**定义 13.3（固定读数协议的合法割）。** 给有限偏序集 $(E,\le)$；$e\in E$ 是带来源身份的事件，具有读数 $X_e:\Omega\to\mathcal X_e$。同一 $\omega$ 同时规定全部这些读数，允许的取得动作不改变它们。记 $\mathcal J(E)$ 为序理想全体：$I\subseteq E$ 属于 $\mathcal J(E)$，意为 $e\in I,d\le e$ 蕴含 $d\in I$。称其为合法割，并定义
$$
q_I(\omega)=\bigl(C(\omega),(X_e(\omega))_{e\in I}\bigr),
\qquad B_I=q_I[\Omega].
\tag{13.3}
$$
乘积按事件索引，不按书写次序索引。事件 $e$ 在 $I$ 启用，意为 $e\notin I$ 且每个 $d<e$ 已在 $I$；写 $I+e=I\cup\{e\}$。两个不同事件同时启用时必不可比。此偏序只规定动作先后是否合法；它不规定读数的概率独立性。若实际动作会扰动后续读数，须另给包含该动作及实际结果的实现与历史；这里固定读数的假设本身不提供这种模型。把运动作为动作时，同样须指定它改变哪些合法取得映射、实际结果或扰动关系。

**定理 13.4（保留前缀、取得关系与确定性细化障碍）。** 对合法割 $I\subseteq J$，存在唯一满射 $r_{JI}:B_J\to B_I$ 使 $r_{JI}q_J=q_I$。对 $I\subseteq J\subseteq K$，
$$
r_{II}=\operatorname{id}_{B_I},\qquad
r_{KI}=r_{JI}r_{KJ},\qquad
\ker q_J\subseteq\ker q_I.
\tag{13.4}
$$
从旧记录到新记录的实际取得关系为
$$
\mathcal R_{IJ}:=\{(q_I\omega,q_J\omega):\omega\in\Omega\}
=\{(b,d)\in B_I\times B_J:b=r_{JI}(d)\}.
\tag{13.5}
$$
按先 $\mathcal R_{IJ}$ 后 $\mathcal R_{JK}$ 的关系复合约定，有 $\mathcal R_{JK}\circ\mathcal R_{IJ}=\mathcal R_{IK}$。存在全定义确定性映射 $u:B_I\to B_J$ 满足 $q_J=uq_I$，当且仅当 $\ker q_I\subseteq\ker q_J$；在保留式记录下，这恰为两核相等。因而只以旧记录为输入的确定性更新不能严格细化实际信息。

**证明。** $r_{JI}$ 删除不属于 $I$ 的事件坐标，保留 $C$。任取 $b=q_I\omega$，$q_J\omega$ 是其原像，故满射；$q_J$ 满射到实际像又给唯一性。重复删除给复合式；若 $q_J$ 相等，其前缀相等，故核包含成立。

式（13.5）的左侧必满足右侧等式。反之，对 $d\in B_J$ 取 $\omega$ 使 $q_J\omega=d$，则 $q_I\omega=r_{JI}(d)=b$。复合关系中的中间项必为 $r_{KJ}(d)$，所以其存在恰要求 $b=r_{JI}r_{KJ}(d)=r_{KI}(d)$，得精确复合。这里使用了同一份 $\Omega$、实际像和嵌套前缀。

若 $q_J=uq_I$，旧记录相等必给新记录相等。反之，所述核包含使 $u(q_I\omega):=q_J\omega$ 与代表无关；它定义在整个 $B_I$。结合已经证明的反向包含即得等核判据。$\square$

**命题 13.5（策略、实际结果与保留读数）。** 设当前完整历史 $H$ 保留 $C$、已取得的带来源读数及任务所需的动作信息。确定性策略取 $a=\pi(H)$，取得动作产生实际结果 $Y$ 后，保留式更新为
$$
H'=(H,a,Y).
\tag{13.6}
$$
若存在同一旧历史而不同 $Y$ 的两个合法实现，则 $H'$ 不能是仅以 $H$ 为输入的确定性函数。另一方面，对 $I\subseteq J$，每个旧读数 $f=h(q_I)$ 都满足
$$
f=(h\circ r_{JI})(q_J).
\tag{13.7}
$$

**证明。** 相同 $H$ 给相同 $a$，不同 $Y$ 给不同有序三元组，违反函数的单值性。若规定 $Y=g(H,a)$，得到的只是这个规则规定的值；它与实际取得结果相等还须在全部合法实现上验证。若结果随机，须给包含旧记录及来源的联合律；结果核来自该律在正概率历史上的条件分布。随机策略所用的随机记录亦须按其实际可访问性纳入历史。式（13.7）由 $r_{JI}q_J=q_I$ 代入得到；它保持已经取得的函数值，不断言微观状态不变。$\square$

**引理 13.6（合法枚举的相邻交换连通性）。** 对有限偏序集的两个合法割 $I\subseteq J$，从 $I$ 到 $J$ 每次加入一个启用事件的路径，恰对应诱导偏序 $J\setminus I$ 的线性扩张。任意两条这样的路径可由有限次相邻不可比事件交换连接，每次交换仍给合法路径。

**证明。** 路径必须把每个前驱先于其后继加入，故给线性扩张。反之，按线性扩张添加元素时，新元素在 $J$ 内的前驱或已在 $I$，或位于扩张中更早的位置；$J$ 为理想保证它没有位于 $J$ 外的前驱，故每步合法。有限非空偏序必有极小元，否则不断取严格更小元会在有限集内造成严格序循环；逐次取出极小元，便给至少一条线性扩张。

取目标扩张的首项 $a$。在另一扩张中，位于 $a$ 之前而需要被它越过的任何 $b$ 都与 $a$ 不可比：若 $b<a$，目标不能以 $a$ 开头；若 $a<b$，另一扩张不能以 $b$ 先于 $a$。逐次向左交换使 $a$ 到达首位，每次只交换不可比相邻项，仍是线性扩张。固定共同首项，在剩余有限偏序上归纳；空集终止。对于路径的每次局部交换，这两个事件在共同前缀后均已启用，因此交换对应一个合法方块。$\square$

**定义 13.7（一般因果割上的指定边界）。** 在同一有限偏序 $E$ 上，对每个 $I\in\mathcal J(E)$ 给集合 $\mathsf X_I$、$\mathsf B_I$ 及满射 $\beta_I:\mathsf X_I\twoheadrightarrow\mathsf B_I$；对每个在 $I$ 启用的 $e$ 给全定义合法映射
$$
U_{I,e}:\mathsf X_I\to\mathsf X_{I+e}.
\tag{13.8}
$$
这些集合不必是定义13.3的实际读数空间。指定边界任务形如 $h_I\beta_I$；某个后续操作可在边界执行，意为它在对应边界纤维上具有一致结果。这是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第120节“可组合关系的最小行为表示与保真辅助构造”中任务商的有限割型情形；表示及后续操作的共同运输采用其第133节“共同实现、概率与演化的同步运输”、第134节“关系表示的探针充分性与三种闭合”的类型约定。

**定理 13.8（边下降与可观察方块的充要性）。** 定义13.7的数据具有唯一的边界映射族 $\overline U_{IJ}:\mathsf B_I\to\mathsf B_J$，使每条边下降、每条合法路径的诱导复合只依赖端点，并满足
$$
\overline U_{II}=\operatorname{id}_{\mathsf B_I},\qquad
\overline U_{IK}=\overline U_{JK}\overline U_{IJ}
\quad(I\subseteq J\subseteq K),
\tag{13.9}
$$
当且仅当以下两项成立。第一，每条边保边界纤维：
$$
\beta_I(x)=\beta_I(x')
\Longrightarrow
\beta_{I+e}(U_{I,e}x)=\beta_{I+e}(U_{I,e}x').
\tag{13.10}
$$
第二，每个合法割 $I$ 及每对不同的同时启用事件 $e,f$ 满足可观察方块等式：
$$
\beta_{I+e+f}U_{I+e,f}U_{I,e}
=
\beta_{I+e+f}U_{I+f,e}U_{I,f}
\quad\text{作为 }\mathsf X_I\to\mathsf B_{I+e+f}\text{ 的映射}.
\tag{13.11}
$$
此结论只运输已指定的边界任务及能够通过边界下降的后续操作。

**证明。** 在式（13.10）下定义
$$
\overline U_{I,I+e}(\beta_Ix):=\beta_{I+e}(U_{I,e}x).
$$
纤维一致性给良定义，满射性给全定义及唯一性。将两条边下降式接续，再用式（13.11），得到两条边界方块复合在每个 $\beta_Ix$ 上相同；满射性使两映射在全部 $\mathsf B_I$ 上相同。

任取从 $I$ 到 $J$ 的两路径。引理13.6把它们连接为相邻方块交换。交换前缀不变，方块在边界上的输出相同，交换后的任意共同后缀由边界映射继续作用，输出仍相同。等价地，在完整状态上，方块两条路产生的状态只需具有相同 $\beta$ 值；式（13.10）逐步把这种相等沿后缀传播，不要求完整状态相等。因此全部路径诱导同一 $\overline U_{IJ}$。空路径给恒等；将两段路径连接给式（13.9）。任何满足要求的族在边上已唯一，在路径复合上也唯一。

反之，边界边映射存在立即给式（13.10）。两条合法二步路径具有同端点，路径无关给边界方块相等，再与 $\beta_I$ 复合得式（13.11）。对任务 $h_J\beta_J$，末端取 $h_J$ 即得任务值不变；后续操作只有满足相应下降条件才能沿同一论证接续。一般原状态读数未必因子化，故不在此量词内。特别地，本定理的确定性运输不生成新取得结果；若把边界解释为保留式实际记录，还必须满足定理13.4的等核障碍，或另把实际结果作为输入。$\square$

**命题 13.9（完整更新不交换而指定边界方块交换）。** 取二元反链 $E=\{e,f\}$，对每个割令 $\mathsf X_I=\{0,1\}^2$、$\mathsf B_I=\{0,1\}$，$\beta_I(b,z)=b$。事件 $e$ 的每条边执行 $(b,z)\mapsto(b,1-z)$，事件 $f$ 的每条边执行 $(b,z)\mapsto(b,0)$。全部边下降且可观察方块交换，但完整更新方块不交换。

**证明。** 两类操作都保留第一坐标，所以每条边的边界映射为恒等，式（13.10）及（13.11）成立。先 $e$ 后 $f$ 的第二坐标为 $0$，先 $f$ 后 $e$ 的第二坐标为 $1$，故完整状态不同。$\square$

**命题 13.10（来源索引档案与时间顺序档案）。** 在定义13.3下，同一合法割 $I$ 的任何合法枚举都给相同 $q_I$。若 $I$ 含有两个不可比事件且任务还要求时间顺序档案
$$
A_\ell(\omega)=\bigl(C(\omega),((e_1,X_{e_1}(\omega)),\ldots,(e_m,X_{e_m}(\omega)))\bigr),
\tag{13.12}
$$
其中 $\ell=(e_1,\ldots,e_m)$ 是所用枚举，则存在两个合法枚举，在同一 $\omega$ 上给出相同 $q_I(\omega)$ 而不同的 $A_\ell(\omega)$。

**证明。** $q_I$ 的 $e$ 坐标始终为同一个 $X_e(\omega)$，枚举不改变事件身份或值。在 $I$ 中取不可比的 $e,f$。在 $I$ 的严格偏序中分别加入 $e<f$ 或 $f<e$ 并取传递闭包；若前者产生环，原偏序必已有从 $f$ 到 $e$ 的路径，后者同理，均与不可比性矛盾。因此两者仍为有限偏序，各自逐次选取剩余极小元得到线性扩张，给出 $I$ 的两个合法枚举，分别使 $e$ 先于 $f$ 和 $f$ 先于 $e$。固定同一来源点 $\omega$，二者给出相同的 $q_I(\omega)$，而式（13.12）的事件标签顺序不同，即使读数值相同，序列仍不同。因此来源索引档案满足的交换等式不能自动用于需要时间顺序的任务；保留该任务时，档案须包含枚举。$\square$

**命题 13.11（共同来源的纤维交与成对盲区）。** 对任意有限族合法割 $I_t$ 与候选记录 $b_t\in B_{I_t}$，它们有同一实际实现，当且仅当
$$
\bigcap_t q_{I_t}^{-1}(\{b_t\})\ne\varnothing.
\tag{13.13}
$$
即使各对候选都有共同实现，也不保证式（13.13）。

**证明。** 交集的元素恰为同时产生全部记录的 $\omega$。取 $\Omega=\{0,1\}^2$，$C$ 常值，三个事件为反链，读数为 $a,b,a\mathbin\oplus b$。任意两读数的联合映射都满射到 $\{0,1\}^2$：给 $a$ 与 $a\oplus b$ 可唯一解出 $b$，其余两种情形同理。但候选三元组 $(0,0,1)$ 无实现，因 $0\oplus0=0$。其三个指定单坐标纤维两两相交而共同交为空。这是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第124节“共同来源的拼接、补全与归一化”中实际像限制的有限例；定理13.4的嵌套复合不授权跨不相关实现拼接。$\square$

**定义 13.12（局部事件费用与端点钟）。** 对每条启用边给 $c(I,e)\in[0,\infty)$。路径费用是其边费用之和。端点钟是函数 $\tau:\mathcal J(E)\to\mathbb R$，满足 $\tau(\varnothing)=0$ 及
$$
\tau(I+e)-\tau(I)=c(I,e).
\tag{13.14}
$$
也允许固定有限维非负向量费用，等式逐坐标解释。这些钟计量指定事件费用；未指定任何衰减、波动或场方程。

**定理 13.13（费用方块与端点势）。** 定义13.12的端点钟存在且唯一，当且仅当每对不同同时启用事件满足
$$
c(I,e)+c(I+e,f)=c(I,f)+c(I+f,e).
\tag{13.15}
$$
此时任意 $I\subseteq J$ 的合法路径费用均为 $\tau(J)-\tau(I)$，且 $\tau$ 随割包含单调。向量费用的结论逐坐标成立。

**证明。** 若端点钟存在，两条二步路径的增量均望远镜求和为 $\tau(I+e+f)-\tau(I)$，故式（13.15）必要。反之，从空割沿任意合法路径到 $I$，以其费用和定义 $\tau(I)$。引理13.6给路径间的相邻交换连通性；每次交换由式（13.15）保持和，故定义无关路径。延长一条路径便得式（13.14）。任意候选钟沿该路径求和得到同一值，所以唯一。任意 $I$ 到 $J$ 的路径上再望远镜求和得端点差；非负费用给单调性。有限向量的每个坐标独立适用同一证明。$\square$

**命题 13.14（共同约束下的多个事件钟与标量次序）。** 对事件子集 $L_1,\ldots,L_m\subseteq E$，令 $\tau_j(I)=|I\cap L_j|$。它们同时满足定理13.13，边增量为 $\mathbf1_{e\in L_j}$，不必彼此相等。有限偏序总有严格保先后次序的标量时间戳；但若有不可比元素，则不存在实值 $t$ 满足
$$
e\le f\iff t(e)\le t(f)\quad\text{对全部 }e,f\in E.
\tag{13.16}
$$
这不排除标量对有限数据的单射编码。

**证明。** 加入 $e$ 时计数增量就是所给指标，交换两次加入的总增量相同。例如二元反链取 $L_1=\{e\},L_2=\{f\}$，四个割的钟向量为 $(0,0),(1,0),(0,1),(1,1)$，两只钟同属一份割结构。逐次选剩余偏序的极小元得到线性扩张；以位置为时间戳，$e<f$ 蕴含 $t(e)<t(f)$。若 $e,f$ 不可比，实数全序仍使 $t(e)\le t(f)$ 或 $t(f)\le t(e)$，反映次序将错误地强迫一次比较，故式（13.16）不可能。上述四个割也可用 $\mathbf1_{e\in I}+2\mathbf1_{f\in I}$ 编为 $0,1,2,3$ 并唯一解码；这个单射并不反映割包含的偏序。$\square$

**命题 13.15（相同事件计数不保证更新方块）。** 在 $\{0,1\}$ 上令 $A(x)=1-x$、$B(x)=0$，并允许两个事件以任一次序各执行一次。两条路径的事件计数及单位总费用相同，末端读数却不同。

**证明。** $B(A(x))=0$ 而 $A(B(x))=1$。两条路径均各计一次 $A$、一次 $B$，总费用均为 $2$。因此费用方块可以成立而状态或指定输出的方块失败；时钟值不能替代定理13.8的可观察方块条件。$\square$

## 14. 给定完整记录的交互分解与合法显露几何

**定义 14.1（同律条件投影与隐藏余项）。** 在定义13.1、13.3的同一个有限 $\Omega$ 上固定概率律 $\mu$。以下实 Hilbert 空间为 $\mathcal H=L^2(\Omega,\mu;\mathbb R)$，把零概率点上的差别识别；算子恒等及函数恢复均按此约定解释。对任意 Boolean 子集 $S\subseteq E$，定义
$$
\mathcal F_S=\sigma(C,X_e:e\in S),\qquad
P_Sf=\mathbb E_\mu[f\mid\mathcal F_S],\qquad
P_\varnothing=P_C,\qquad Q=\operatorname{Id}_{\mathcal H}-P_E.
\tag{14.1}
$$
这里 $C$ 始终是全部已表示旧记录的商；$P_C$ 不一般是常数投影。$P_S$ 是到 $\mathcal F_S$ 可测函数空间的正交投影。具体地，在正概率记录纤维 $F$ 上，$P_S f$ 等于 $\sum_{\omega\in F}\mu(\omega)f(\omega)/\mu(F)$；逐纤维求和显示 $f-P_Sf$ 与所有纤维常值函数正交，从而给该投影刻画。$S$ 不为理想时，$P_S$ 仅是用于分解的数学辅助算子，不宣告这些事件可单独合法取得。$Q$ 保留全部具名记录仍未观察到的方向。

对 $f\in\mathcal H$，定义积分均方风险
$$
\mathscr R_I(f)=\|f-P_If\|_2^2
=\sum_{\omega\in\Omega}\mu(\omega)|f(\omega)-P_If(\omega)|^2
\quad(I\in\mathcal J(E)).
\tag{14.2}
$$
它对全部实现积分，不是某次实际记录取值上的条件方差。固定这份 $\mu$ 是风险比较的共同前提。

**定理 14.2（任意依赖下的 Boolean 反演）。** 定义自伴算子
$$
D_S=\sum_{T\subseteq S}(-1)^{|S|-|T|}P_T,
\qquad D_\varnothing=P_C.
\tag{14.3}
$$
无需任何独立性，就有
$$
P_A=\sum_{S\subseteq A}D_S\quad(A\subseteq E),\qquad
\operatorname{Id}_{\mathcal H}=Q+\sum_{S\subseteq E}D_S.
\tag{14.4}
$$
在任意依赖下，这只是算子加法恒等式，不断言各 $D_S$ 是正交投影。

**证明。** 将式（14.3）代入第一式的右侧，$P_T$ 的系数为
$$
\sum_{T\subseteq S\subseteq A}(-1)^{|S|-|T|}
=(1-1)^{|A\setminus T|},
$$
它在 $T=A$ 时为 $1$，其余为 $0$。再用 $Q=\operatorname{Id}-P_E$ 得第二式。自伴性来自各 $P_T$ 自伴及系数实值。这是 Boolean 格的 Möbius 反演；在乘积测度的函数 ANOVA 中，同一反演见 Art B. Owen，*Monte Carlo theory, methods and examples*，附录 [The ANOVA decomposition of $[0,1]^d$](https://artowen.su.domains/mc/A-anova.pdf)，§A.4，式（A.11）—（A.12）。$\square$

**命题 14.3（合法观察塔的正交增量）。** 对嵌套合法割
$\varnothing=I_0\subseteq I_1\subseteq\cdots\subseteq I_m$，令 $\Delta_k=P_{I_k}-P_{I_{k-1}}$。即使读数相依，各 $\Delta_k$ 仍是两两正交的自伴投影，与 $P_C$ 正交，且
$$
\Delta_k=\sum_{\substack{S\subseteq I_k\\S\nsubseteq I_{k-1}}}D_S,
\qquad
f=P_Cf+\sum_{k=1}^m\Delta_kf+(\operatorname{Id}-P_{I_m})f.
\tag{14.5}
$$
对任意合法割 $I\subseteq J$，
$$
\mathscr R_I(f)-\mathscr R_J(f)=\|(P_J-P_I)f\|_2^2\ge0.
\tag{14.6}
$$

**证明。** $\mathcal F_I\subseteq\mathcal F_J$ 给嵌套可测子空间，故 $P_JP_I=P_I$；取伴随得 $P_IP_J=P_I$。于是 $(P_J-P_I)^2=P_J-P_I$，且它自伴。对 $k<\ell$ 展开 $\Delta_k\Delta_\ell$，四项按较小下标投影分别抵消为零；同样有 $P_C\Delta_k=0$。式（14.5）第一式从式（14.4）相减，第二式望远镜求和。最后
$$
f-P_If=(f-P_Jf)+(P_J-P_I)f
$$
的两项正交，因为第一项正交于全部 $\mathcal F_J$ 可测函数，第二项属于该空间。取范数平方即得式（14.6）。这正是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第121节“保留式观察的正交增量与记录时间”中§121.4—121.6的观察塔公式，所增加的等式是它与式（14.3）的连接。$\square$

**假设 14.4（相对于完整旧记录的联合条件独立）。** 对每个 $\mu(C=c)>0$ 的类及每个取值元组，要求
$$
\mu(X_E=x_E\mid C=c)
=\prod_{e\in E}p_e(x_e\mid c),\qquad
p_e(x_e\mid c):=\mu(X_e=x_e\mid C=c).
\tag{14.7}
$$
这是全部 $X_e$ 给定 $C$ 后的相互独立，既不以两两独立代替，也不以无条件独立代替。$\Omega$ 可另含未被 $(C,X_E)$ 决定的变量；式（14.7）不假定 $P_E=\operatorname{Id}$。零概率 $C$ 类与乘积权重为零的元组不承担条件等式。

**定理 14.5（逐旧记录纤维的条件 ANOVA）。** 在假设14.4下，对任意 $S,T,A\subseteq E$，
$$
P_SP_T=P_{S\cap T},\qquad
P_AD_S=
\begin{cases}
D_S,&S\subseteq A,\\
0,&S\nsubseteq A.
\end{cases}
\tag{14.8}
$$
全部 $D_S$ 是两两正交的自伴投影，并且 $QD_S=D_SQ=0$。因此
$$
\mathcal H=\operatorname{ran}Q\ \oplus\bigoplus_{S\subseteq E}\operatorname{ran}D_S,
\qquad
\|f\|_2^2=\|Qf\|_2^2+\sum_{S\subseteq E}\|D_Sf\|_2^2.
\tag{14.9}
$$
这是标准 Hoeffding／函数 ANOVA 在固定旧记录纤维上的有限乘积形式。非条件乘积分解及正交性见 Owen 所引附录§A.2—A.3，尤其引理A.3—A.4；[QUANTUM-RH 卷](QUANTUM-RH.md)题为“三十一、把 $5040$ 的 $(4,2,1,1)$ 从‘指数向量’提升为真正的交互几何”的一节也使用其有限寄存器形式。这里保留变化的条件权重、完整 $C$ 与 $Q$。

**证明。** 任取 $f\in\mathcal H$，先令 $g=P_Ef$。由嵌套塔式关系，对所有 $S$ 有 $P_Sf=P_Sg$，所以隐藏变量先通过 $g$ 的全记录条件平均进入计算。固定正概率 $c$，把 $g$ 写成全记录上的函数 $g(c,x_E)$。式（14.7）使正概率记录支撑恰为各正条件边缘支撑的乘积；在该支撑上
$$
(P_Sg)(c,x_S)
=\sum_{z_{E\setminus S}}g(c,x_S,z_{E\setminus S})
\prod_{e\notin S}p_e(z_e\mid c).
\tag{14.10}
$$
分母中固定坐标的正权重约去即得此式；零权重项可以删去。

令 $A_0=S\cap T$、$B_0=S\setminus T$、$D_0=T\setminus S$、$F_0=E\setminus(S\cup T)$。先取 $P_Tg$，式（14.10）对 $B_0,F_0$ 求积权平均，结果只依赖 $A_0,D_0$。再取 $P_S$，对 $D_0$ 求平均，已经不出现的 $F_0$ 的权重和为一，已经在第一步消去的 $B_0$ 不会重新出现。合并有限求和恰对 $B_0,D_0,F_0$ 全部求平均，所得是 $P_{A_0}g$。各正概率 $c$ 都成立，故 $P_SP_Tf=P_{S\cap T}f$ 在 $\mathcal H$ 成立。

将这一等式代入 $P_AD_S$。若 $S\subseteq A$，每个 $T\subseteq S$ 有 $A\cap T=T$，故得 $D_S$。否则选 $e\in S\setminus A$，在式（14.3）中将不含 $e$ 的 $T$ 与 $T\cup\{e\}$ 配对；二者交 $A$ 后相同而符号相反，所以和为零。

为证明投影性，对每个 $S$ 有算子乘积表示
$$
D_S=P_S\prod_{e\in S}\bigl(\operatorname{Id}-P_{E\setminus\{e\}}\bigr).
\tag{14.11}
$$
展开右侧，对选择的 $R\subseteq S$ 使用已经证明的交集乘法律，得到 $(-1)^{|R|}P_{S\setminus R}$，总和即式（14.3）；$S=\varnothing$ 时为空乘积。右侧各因子均为互相交换的自伴投影，所以乘积自伴且平方等于自身。

若 $S\ne T$，交换二者名称后可取 $e\in S\setminus T$。由式（14.8），$P_TD_S=0$，而 $D_T=P_TD_T=D_TP_T$，故 $D_TD_S=0$；取伴随得反向复合也为零。又 $P_ED_S=D_S$，故与 $Q$ 正交。式（14.4）已给这些投影之和为恒等，因而得到直和；分量的存在来自该算子恒等式，唯一性与范数公式来自正交性。$\square$

**定义 14.6（按因果下闭包分组的交互算子）。** 对 $S\subseteq E$ 定义
$$
\downarrow S=\{d\in E:\exists e\in S,\ d\le e\},\qquad
K_J=\sum_{\substack{S\subseteq E\\\downarrow S=J}}D_S
\quad(J\in\mathcal J(E)).
\tag{14.12}
$$
$K_J$ 按包含索引集 $S$ 所需的最小合法割 $J=\downarrow S$ 对 Boolean 交互分组；$K_\varnothing=D_\varnothing=P_C$。记 $\operatorname{Max}(J)$ 为 $J$ 的极大元集合，$\operatorname{Max}(\varnothing)=\varnothing$。

**定理 14.7（合法割上的反演与增量）。** 在任意联合律下，
$$
P_I=\sum_{\substack{J\in\mathcal J(E)\\J\subseteq I}}K_J,
\qquad
K_J=\sum_{R\subseteq\operatorname{Max}(J)}(-1)^{|R|}P_{J\setminus R}.
\tag{14.13}
$$
后式的每个 $J\setminus R$ 都是合法割。对合法 $I\subseteq I'$，
$$
P_{I'}-P_I
=\sum_{\substack{J\in\mathcal J(E)\\J\subseteq I',\ J\nsubseteq I}}K_J.
\tag{14.14}
$$
在假设14.4下，各 $K_J$ 是两两正交的自伴投影，$P_E=\sum_JK_J$；它们与 $Q$ 正交。

**证明。** 因 $I$ 为理想，$S\subseteq I$ 当且仅当 $\downarrow S\subseteq I$。按此下闭包分组式（14.4），得到第一式；相减得到式（14.14）。

从理想中只删除极大元仍为理想：若 $x\in J\setminus R$ 且 $y\le x$，则 $y\in J$；若 $y\in R$，其极大性迫使 $y=x$，与 $x\notin R$ 矛盾。把式（14.4）代入式（14.13）第二式的右侧，某个 $D_S$ 在 $S\subseteq J$ 时的系数为
$$
\sum_{R\subseteq\operatorname{Max}(J)\setminus S}(-1)^{|R|},
$$
否则为零。该和恰在 $\operatorname{Max}(J)\subseteq S\subseteq J$ 时为 $1$。有限理想的每个元素都在某个极大元之下，故这一条件蕴含 $\downarrow S=J$。反之，若 $\downarrow S=J$，任意极大元 $m$ 必满足 $m\le s$ 对某个 $s\in S\subseteq J$ 成立，极大性给 $s=m$，所以全部极大元属于 $S$。系数恰选出定义14.6中的项，证明所需公式。

在条件乘积假设下，定理14.5的正交投影被分成互不相交的有限组；每组之和仍自伴幂等，不同组乘积为零，且每项都与 $Q$ 正交。第二式是这个序理想格的具体反演公式，其符号只沿被删除的极大元子集使用，不能换成对所有子理想一律赋 $(-1)^{|J|-|I|}$。$\square$

**命题 14.8（反链、链与分支割的具体分组）。** 若 $E$ 为反链，则 $K_J=D_J$。若 $E=\{e_1<\cdots<e_n\}$ 为链，令 $I_k=\{e_1,\ldots,e_k\}$，则
$$
K_{I_k}=P_{I_k}-P_{I_{k-1}}\quad(1\le k\le n).
\tag{14.15}
$$
链中的这些 $K$ 在任意依赖下已是正交投影。若 $E=\{a,b,c\}$，仅有 $a<b,a<c$，则非空合法割为 $a,ab,ac,abc$，下标用连写表示子集，有
$$
\begin{aligned}
K_a&=D_a,\qquad K_{ab}=D_b+D_{ab}=P_{ab}-P_a,\\
K_{ac}&=D_c+D_{ac}=P_{ac}-P_a,\\
K_{abc}&=D_{bc}+D_{abc}=P_{abc}-P_{ab}-P_{ac}+P_a.
\end{aligned}
\tag{14.16}
$$

**证明。** 反链的每个子集等于自身的下闭包，故分组不改变单项。链的非空理想只有一个极大元 $e_k$，式（14.13）只有保留和删除它两项，给式（14.15）；命题14.3给正交性而不需要条件独立。分支偏序的下闭包分别把 $\{b\},\{a,b\}$ 并为 $ab$，把 $\{c\},\{a,c\}$ 并为 $ac$，把 $\{b,c\},\{a,b,c\}$ 并为 $abc$，其余项不变。顶割的极大元为 $b,c$，删除它们的四种方式给式（14.16）最后一个等式。对于一般分支偏序，定理14.5的条件独立是使全部这些组正交的一项充分条件；链的结论不要求把这项充分条件当成必要条件。$\square$

**定理 14.9（目标恢复与含隐藏余项的积分风险）。** 在假设14.4下，对任意 $f\in\mathcal H$ 和合法割 $I$，以下三个条件等价：
$$
\begin{aligned}
f=P_If
&\iff \bigl[Qf=0\ \text{且}\ D_Sf=0\text{ 对每个 }S\nsubseteq I\bigr]\\
&\iff \bigl[Qf=0\ \text{且}\ K_Jf=0\text{ 对每个 }J\in\mathcal J(E),\ J\nsubseteq I\bigr].
\end{aligned}
\tag{14.17}
$$
它们也等价于存在 $h:B_I\to\mathbb R$ 使 $f=h(q_I)$ 在 $\mu$ 几乎处处成立。并且
$$
\mathscr R_I(f)
=\|Qf\|_2^2+\sum_{S\nsubseteq I}\|D_Sf\|_2^2
=\|Qf\|_2^2+\sum_{\substack{J\in\mathcal J(E)\\J\nsubseteq I}}\|K_Jf\|_2^2.
\tag{14.18}
$$
对 $I\subseteq I'$ 的风险下降为
$$
\mathscr R_I(f)-\mathscr R_{I'}(f)
=\sum_{\substack{S\subseteq I'\\S\nsubseteq I}}\|D_Sf\|_2^2
=\sum_{\substack{J\subseteq I',\ J\nsubseteq I\\J\in\mathcal J(E)}}\|K_Jf\|_2^2.
\tag{14.19}
$$

**证明。** 式（14.4）给
$$
f-P_If=Qf+\sum_{S\nsubseteq I}D_Sf.
$$
各项由定理14.5互相正交；同样按下闭包分组，定理14.7给 $Qf+\sum_{J\nsubseteq I}K_Jf$。两次取范数平方得到式（14.18），有限个非负平方和为零恰为每一项为零，所以得到式（14.17）。条件期望投影的像是 $\mathcal F_I$ 可测函数类；有限空间中，这等价于在各正概率 $q_I$ 纤维上几乎处处常值。以该值定义 $h$，在零概率纤维上任意扩展，便得因子化；反向由可测性立得。相减式（14.18）给式（14.19）。

若 $\mu$ 对 $\Omega$ 全支撑，几乎处处等式就是逐点等式。否则若要对全部 $\Omega$ 作逐点恢复，仍须另验集合意义上的 $q_I$ 纤维常值性。此处结论针对指定 $f$ 与指定律，不由目标风险给出内部参数稳定重建、任意维度实现的唯一性或物理空间度量。去掉假设14.4后仍保留命题14.3的嵌套风险恒等式，但本证明不再给按 $D_S$ 或一般 $K_J$ 分项的平方和。$\square$

**定理 14.10（合法次序决定显露时刻而不改变最终空间）。** 给 $E$ 的一个合法全枚举 $\ell=(e_1,\ldots,e_n)$，令 $I_k=\{e_1,\ldots,e_k\}$。对非空 $S\subseteq E$ 定义
$$
\rho_\ell(S)=\max\{k:e_k\in S\}.
\tag{14.20}
$$
它既是首次包含 $S$ 的割下标，也是首次包含 $\downarrow S$ 的割下标。任意联合律下有
$$
\Delta_k=P_{I_k}-P_{I_{k-1}}
=\sum_{\rho_\ell(S)=k}D_S
=\sum_{\substack{J\subseteq I_k,\ J\nsubseteq I_{k-1}\\J\in\mathcal J(E)}}K_J.
\tag{14.21}
$$
在假设14.4下，非零 $D_S$ 的空间在 $\rho_\ell(S)$ 之前与当前观察空间正交，在该时刻起被完全包含；且
$$
\sum_{k=1}^n\|\Delta_k f\|_2^2
=\|P_Ef-P_Cf\|_2^2
=\mathscr R_\varnothing(f)-\mathscr R_E(f)
=\sum_{\varnothing\ne S\subseteq E}\|D_Sf\|_2^2.
\tag{14.22}
$$
左边按取得时刻分配的各项可以随合法枚举变化，最终空间 $\operatorname{ran}P_E$ 和总风险下降不变。式（14.22）前三项的相等无需条件独立。

**证明。** $I_k$ 包含 $S$ 恰在其最后一个成员取得后；因 $I_k$ 为理想，包含 $S$ 与包含 $\downarrow S$ 等价。式（14.21）来自命题14.3及定理14.7。在条件乘积情形，式（14.8）给 $P_{I_k}D_S$ 在 $S\nsubseteq I_k$ 时为零，在 $S\subseteq I_k$ 时为 $D_S$，即所述正交及包含。式（14.22）前两个等号由命题14.3的正交增量与式（14.6）望远镜求和得到；最后一个等号由 $P_E-P_C=\sum_{S\ne\varnothing}D_S$ 的正交性得到。端点不依赖枚举，故总量不变。

这里每个枚举事先固定，比较中读数函数与概率律也固定。若下一事件由当前记录自适应选择，实际割及顺序成为随机历史的一部分；本式不提供未经相应历史条件化的自适应 ANOVA 公式。[QUANTUM-RH 卷](QUANTUM-RH.md)题为“三十五、现在把‘空间阶数’与‘离散时间’真正放到一张图里”的一节控制演化算子在交互阶数间的有限传播；其传播步数与这里固定读数的取得次序是不同索引。$\square$

**命题 14.11（相同最终任务的两种显露分配与联合读数）。** 取 $\Omega=\{-1,1\}^2$ 上均匀律，$u,v$ 为独立坐标，$C$ 常值，$E$ 为读 $u,v$ 的二元反链，$f=u+uv$。先读 $u$ 后读 $v$ 的两次增量平方范数为 $(1,1)$；反向为 $(0,2)$。此外，$uv$ 属于联合读数空间，却正交于两个单坐标读数空间之和。

**证明。** 四点上的 $1,u,v,uv$ 构成正交归一基：每个非空坐标乘积的均值为零，其平方为一，不同乘积的内积仍为一个非空乘积的均值。故
$$
P_Cf=0,\qquad P_uf=u,\qquad P_vf=0,\qquad P_{uv}f=f.
$$
前向增量为 $u,uv$，各平方范数为 $1$；反向为 $0,u+uv$，平方范数为 $0,2$。单坐标的全部可测函数分别为 $\operatorname{span}\{1,u\}$ 与 $\operatorname{span}\{1,v\}$，其和不包含非零且与它正交的 $uv$。但 $\sigma(u,v)$ 给全部四点，故 $uv$ 联合可测。因此联合 $\sigma$ 代数的函数空间不同于边缘函数空间的线性和。此 Walsh 区分采用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§28.3“受限线性读出的历史关系容量”、§28.4“可逆重编码保持信息，却改变受限可访问性”的共同函数空间解释。$\square$

**命题 14.12（已获 XOR 记录破坏无条件乘积的交互正性）。** 环境恰取 $\Omega=\{0,1\}^2$，均匀律下 $X,Y$ 为坐标，完整旧记录为 $C=X\mathbin\oplus Y$，之后两个具名读数为 $X,Y$。虽然 $X,Y$ 无条件独立，仍有
$$
P_{\{X\}}=P_{\{Y\}}=P_{\{X,Y\}}=\operatorname{Id}_{\mathcal H},\qquad
D_{\{X,Y\}}=P_C-\operatorname{Id}_{\mathcal H}.
\tag{14.23}
$$
后者在非零的 $\operatorname{ran}(\operatorname{Id}-P_C)$ 上具有严格负二次型，因而不是正交投影。任一嵌套取得顺序的风险改善仍非负。

**证明。** 给定 $(C,X)$ 可由 $Y=C\oplus X$ 恢复整个点；给定 $(C,Y)$ 同理，所以前三个投影均为恒等。代入式（14.3）给 $D_{\{X,Y\}}=\operatorname{Id}-\operatorname{Id}-\operatorname{Id}+P_C$。若 $P_Cg=0$ 且 $g\ne0$，则 $\langle g,D_{\{X,Y\}}g\rangle=-\|g\|_2^2<0$；例如 $g=(-1)^X$，在每个奇偶类上取两种符号且等权，故 $P_Cg=0$、$\|g\|_2^2=1$。给定 $C=0$ 时 $X=Y$，且各自仍为公平位，联合并不等于条件边缘的乘积，明确违反假设14.4。

沿任一种顺序，两个塔增量均依次为 $\operatorname{Id}-P_C$ 与 $0$，所以命题14.3给非负风险下降。若另扩充环境加入未观察变量，前三个投影只能由上述记录确定为 $P_E$，不能自动写成环境上的恒等；这里限定为恰好四点保证了式（14.23）。$\square$

**命题 14.13（记录交互全部为零仍有隐藏目标）。** 取 $\Omega=\{-1,1\}^3$ 上均匀律，坐标 $u,v,z$ 独立，$C$ 常值，事件只记录 $u,v$。对目标 $f=z$，假设14.4成立，但
$$
D_Sf=0\quad(S\subseteq\{u,v\}),\qquad
K_Jf=0\quad(J\in\mathcal J(E)),\qquad
Qf=f,\quad\|Qf\|_2^2=1.
\tag{14.24}
$$

**证明。** 给定 $u,v$ 的任意子集后，$z$ 仍独立且均值为零，故每个 $P_Sf=0$。式（14.3）及（14.12）给全部所列 $D_Sf,K_Jf$ 为零，而 $P_Ef=0$ 给 $Qf=f$；$z^2=1$ 给范数平方为一。因此即使全部已记录交互都没有未显露能量，也不能删除定理14.9中的 $Qf=0$ 条件。$\square$

## 14.99 追加锚

## 15. 有限受控预测接口与实际概率域的几何

**约定 15.1（联合仪器、完整档案与预测任务）。** 以下三节是普通数学推导；所用成熟结果在使用处注明来源，不宣称新增 Lean 核验或世界范围原创。第13—14节的固定、不扰动读数族在此扩展为会改变后继状态的受控实验。取有限非空集合 $X,A,Y$，分别表示隐藏当前状态、动作和输出，令 $n=|X|$。给非负矩阵
$$
K_{a,y}\in\mathbb R^{X\times X},\qquad
\sum_{y\in Y}K_{a,y}\mathbf1=\mathbf1\quad(a\in A).
\tag{15.1}
$$
所有 $a$ 在每个状态均合法；若要表示失败或终止，须把其输出及后继吸收状态纳入这同一个仪器，完整记录保留这些标签。记 $\Delta_X=\{p\in\mathbb R^X:p_x\ge0,\ \sum_xp_x=1\}$；行向量 $p\in\Delta_X$ 表示当前状态律，矩阵作用于列函数。带输出的动作词 $w=(a_1,y_1)\cdots(a_k,y_k)$ 按时间先后定义
$$
K_w=K_{a_1,y_1}\cdots K_{a_k,y_k},\qquad
K_\varnothing=I,\qquad pK_w\mathbf1.
\tag{15.2}
$$
末项是固定执行动作词 $(a_1,\ldots,a_k)$ 时取得整个输出词 $(y_1,\ldots,y_k)$ 的概率，不是只看末端输出的边缘。

记 $C$ 为全部已表示的、带来源的旧档案，$H_t$ 为保留 $C$ 的完整可访问历史。允许策略采用独立于初态和环境噪声的外部随机源，并按下列条件核逐步生成联合律：对每个正概率条件事件，
$$
\Pr(A_t=a,Y_{t+1}=y,X_{t+1}=x'\mid
\Theta=\theta,X_t=x,H_t=h)
=\pi_t(a\mid h)K_{a,y}(x,x').
\tag{15.3}
$$
$\Theta$ 是可选的固定来源标签；没有该标签时删去它。给定更早隐藏状态路径时也使用同一右侧，所以式（15.3）是顺序生成契约，不仅是一个孤立的边缘条件等式。随机源初始独立不能替代此受支撑条件化契约。记录按 $H_{t+1}=(H_t,A_t,Y_{t+1})$ 扩充；若控制器还访问其他随机记录或内部记忆，须将其相应信息包含在所声明的访问历史中。这里采用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定义17.1的联合核语义；其定理17.2—17.3提供完整开环记录与自适应实验的精确接口，命题17.7已经排除了分别拼接输出和后继边缘的替代方案。

正概率分支 $\ell=pK_{a,y}\mathbf1>0$ 的当前状态后验为 $pK_{a,y}/\ell$。这是已声明联合模型中的统计条件化；$K_{a,y}$ 已包含真实状态改变，后验更新不等于免费取得或制备微观状态。$p$ 及下文的 $s$ 只是任务工作接口，完整档案 $C$ 和控制器访问权另行保留。本节的有限预测表示沿用 Michael L. Littman、Richard S. Sutton、Satinder Singh，[*Predictive Representations of State*](https://proceedings.neurips.cc/paper_files/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf)，NeurIPS 14（2001），PDF第7页式（3）、定理1及第7—11页的有限 POMDP 构造；该文第11页也明确给出带负投影系数的例子。

**命题 15.2（全部词的有限不变张成）。** 在约定15.1下，置
$$
V=\operatorname{span}\{K_w\mathbf1:w\text{ 为任意有限词}\},\qquad
V_0=\operatorname{span}\{\mathbf1\},\qquad
V_{j+1}=V_j+\sum_{a,y}K_{a,y}V_j.
\tag{15.4}
$$
则 $V_j$ 恰由长度至多 $j$ 的词列张成；若 $V_{j+1}=V_j$，此后全部等于 $V_j=V$。特别地 $V_{n-1}=V$，严格增长至多发生 $n-1$ 次。这是词深度界，不是词个数、采样次数或实验预算界。

**证明。** $j=0$ 对应空词。归纳时，左乘 $K_{a,y}$ 正好在旧词前加一对动作与输出；连同旧词，得到全部长度至多 $j+1$ 的生成元。若相邻空间相等，则每个 $K_{a,y}$ 都保持 $V_j$，由词长归纳全部词列属于它，故稳定并等于 $V$。否则每步维数至少加一；从维数一开始，在 $n$ 维空间中最多严格增长 $n-1$ 次，得指定深度结论。$n=1$ 时 $V_0=\mathbb R^X$，无需增长。枚举至该深度仍可能涉及 $\sum_{j=0}^{n-1}(|A||Y|)^j$ 个词，且精确取得核或预测值的费用未由此消失。

这是上述 PSR 构造使用的不变张成法，与[量子算术卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)§57的未来 effect 空间、§73的有限 Hankel 实现及[5040卷](ZECKENDORF_EULER_5040.md)“最小线性实现的维数恰好等于这个秩”一段中的加权自动机方法相接。这里的生成元换为联合仪器的全部词；[DynamicClosureMinimality](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)的有限干预轨迹最小闭包供应相应的集合结构，但不直接代替概率核证明。不把既有有限维闭包方法另称为新原理。$\square$

**定理 15.3（预测坐标、正锥与支撑内更新）。** 令 $r=\dim V$，选列基矩阵 $B\in\mathbb R^{X\times r}$，第一列为 $\mathbf1$。记 $e_1$ 为 $\mathbb R^r$ 的第一标准列向量。存在唯一矩阵 $M_{a,y}\in\mathbb R^{r\times r}$ 满足
$$
K_{a,y}B=BM_{a,y}.
\tag{15.5}
$$
定义实际归一化预测域及未归一化正锥
$$
\mathcal P=\{pB:p\in\Delta_X\}
=\operatorname{conv}\{B(x,:):x\in X\},\qquad
\mathcal C=\{uB:u\in\mathbb R^X_{\ge0}\}.
\tag{15.6}
$$
对任意 $s\in\mathcal P$，有 $se_1=1$，且
$$
\ell_{a,y}(s)=sM_{a,y}e_1\ge0,\qquad
\sum_y\ell_{a,y}(s)=1.
\tag{15.7}
$$
当 $\ell_{a,y}(s)>0$ 时，
$$
F_{a,y}(s)=\frac{sM_{a,y}}{\ell_{a,y}(s)}\in\mathcal P
\tag{15.8}
$$
与 $s=pB$ 所选的代表 $p$ 无关。若分支质量为零，则 $sM_{a,y}=0$，而该分支没有由条件化确定的后验。每个 $M_{a,y}$ 保持 $\mathcal C$；其矩阵元素无需逐项非负。

**证明。** 命题15.2给 $K_{a,y}V\subseteq V$，所以 $K_{a,y}B$ 的各列在基 $B$ 中有唯一坐标，得到式（15.5）。对任意 $u\ge0$，
$$
(uB)M_{a,y}=(uK_{a,y})B\in\mathcal C.
$$
若 $s=pB$，则 $se_1=p\mathbf1=1$，且 $sM_{a,y}e_1=pK_{a,y}\mathbf1$；非负性与输出质量和由式（15.1）给出。正质量时 $p'=pK_{a,y}/\ell$ 是概率行向量，$p'B$ 就是式（15.8）。其右侧只依赖 $s,a,y$，因此代表无关。质量为零时非负行向量 $pK_{a,y}$ 的坐标和为零，故它全部为零，进而 $sM_{a,y}=0$；不对 $0/0$ 作后验解释。相同论证还表明 $c\in\mathcal C$ 且 $ce_1=0$ 必有 $c=0$。

对词定义 $M_w=M_{a_1,y_1}\cdots M_{a_k,y_k}$、$M_\varnothing=I$。逐次应用式（15.5）得 $K_wB=BM_w$，故所有词概率为 $sM_we_1$。概率正性由实际锥保证，而非由任意坐标矩阵的符号保证。第15.7条将直接展示负元素。上述归一化公式是所引 PSR 文献式（3）在含常数列的基上的写法；其适用范围始终是 $\mathcal P$，没有把整个超平面 $se_1=1$ 宣告为可实现概率态。$\square$

**定理 15.4（实际预测商、线性维数与可恢复目标）。** 在上述同一仪器下，对任意 $p,q\in\Delta_X$，
$$
pB=qB
\iff \forall w, pK_w\mathbf1=qK_w\mathbf1.
\tag{15.9}
$$
在相同固定初始可访问记录、相同控制器状态及式（15.3）的策略契约下，这还等价于全部允许有限自适应实验的完整动作—输出记录律相等。因而 $\mathcal P$ 表示实际实现的预测等价类；任何能决定全部这些词概率的集合统计量 $T$，在其实际像上唯一决定 $s$。

若竞争表示是未归一化输入上的齐次线性映射 $L:\mathbb R^X\to W$，其中 $W$ 有限维，并且相同 $L(u)$ 对全部 $u\ge0$ 决定相同的每个 $uK_w\mathbf1$，则 $\dim\operatorname{ran}L\ge r$；$u\mapsto uB$ 达到 $r$。归一化域 $\mathcal P$ 的仿射维数恰为 $r-1$。

对任意列函数 $h\in\mathbb R^X$，存在解码器 $g:\mathcal P\to\mathbb R$ 使
$$
g(pB)=ph\quad\text{对全部 }p\in\Delta_X
\quad\Longleftrightarrow\quad h\in V.
\tag{15.10}
$$
特别地，从 $s$ 恢复全部初态分布 $p$ 的充要条件为 $V=\mathbb R^X$。这些是全先验结论；某个受限可达先验族可以有额外关系。

**证明。** $pB=qB$ 使 $p-q$ 消去 $V$，故消去每个词列；反向由生成元张成 $V$ 得到。各输出词的概率相等即为固定动作词下的完整输出律相等。直接应用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理17.2的逐记录策略乘子论证得到自适应等价；初态是混合律时，同一乘子仍与被求和的隐藏状态无关。固定词本身属于策略族，给反向。确定性闭包对应[观察者闭包谱卷](OBSERVER_CLOSURE_SPECTRUM.md)§16；这里不将控制器能读取隐藏状态的策略算入允许族。

若 $T(p)=T(q)$，其预测充分性使式（15.9）右侧成立，故可定义 $\varphi(T(p))=pB$。它良定义且在实际像上唯一，给集合意义的最小性；此为[PredictiveStateUniversalMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.lean)的实际像唯一因子化结构，不是任意编码长度下界。[CanonicalPredictiveStateSufficiency](../../../D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency.lean)的充分性也针对已指定的未来条件律。

对齐次线性下界，取 $d\in\ker L$，将它分成 $d=d^+-d^-$，其中 $d^\pm\ge0$。线性性给 $L(d^+)=L(d^-)$，假设遂给 $dK_w\mathbf1=0$ 对所有词成立，故 $dB=0$。于是 $u\mapsto uB$ 通过 $\operatorname{ran}L$ 线性因子化，而 $B$ 列满秩使其像维数为 $r$，得到下界。归一化方面，$\mathcal P$ 的全部行顶点候选均在 $se_1=1$ 上。固定一个这样的行 $v_0$，其余行之差都在 $se_1=0$；$v_0$ 与差空间线性独立。全部行的线性张成维数为 $r$，所以差空间维数为 $r-1$，正是仿射维数。$r=1$ 时 $\mathcal P$ 是单点。这与[MinimalPredictiveSummary](../../../D5/S3/Quantum/Fibers/MinimalPredictiveSummary.lean)的线性范围维数界、[AllFutureStatisticsSufficiency](../../../D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean)的未来张成判据使用同一线性结构，但载体及生成算子按本节重新指定。

若 $h=B\alpha$，取 $g(s)=s\alpha$ 即可恢复。若 $h\notin V$，有限维线性分离给非零行向量 $d$，满足 $dB=0$ 而 $dh\ne0$；因 $\mathbf1\in V$，有 $d\mathbf1=0$。取内点均匀先验 $p_0$，再取 $\varepsilon>0$ 足够小使 $\varepsilon|d_x|<1/n$ 对所有 $x$ 成立。则 $p_\pm=p_0\pm\varepsilon d\in\Delta_X$，两者预测态相同而目标差为 $2\varepsilon dh\ne0$，排除任何解码器。恢复全部 $p$ 等价于恢复每个坐标指标函数；这些函数张成 $\mathbb R^X$，得最后结论。任意非线性集合编码的实坐标数或位数，均未受这里的线性维数论证约束。$\square$

**定理 15.5（概率单纯形上的目标最小最坏误差）。** 对同一 $B,V$ 及任意 $h\in\mathbb R^X$，允许所有集合函数解码器，有
$$
\inf_{g:\mathcal P\to\mathbb R}
\sup_{p\in\Delta_X}|ph-g(pB)|
=\operatorname{dist}_\infty(h,V)
:=\min_{v\in V}\max_{x\in X}|h_x-v_x|.
\tag{15.11}
$$
右侧的最佳逼近存在，且一个线性读出已达到该误差。该式是在有界概率域上的目标恢复结论；[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理1.4针对无界线性输入得到的无穷风险不能转移到这里。它与该卷§3.1的候选纤维半径公式相容。

**证明。** $V$ 是有限维闭子空间。极小化序列的 $\|h-v\|_\infty$ 有界，故 $\|v\|_\infty$ 有界；取收敛子列，极限仍在 $V$，给最佳 $v_*$。写 $v_*=B\alpha$，则 $g(s)=s\alpha$ 满足
$$
|ph-g(pB)|=|p(h-v_*)|\le\|h-v_*\|_\infty
$$
对每个概率 $p$ 成立，给上界。

令 $d=\operatorname{dist}_\infty(h,V)$。$d=0$ 时上界已给零风险。若 $d>0$，在商空间 $\mathbb R^X/V$ 的 $\ell_\infty$ 商范数下，对非零元 $h+V$ 取范数一的支撑泛函，并延拓到整个商空间。有限维 Hahn–Banach 定理及 $\ell_\infty$ 与 $\ell_1$ 的对偶给行向量 $z$，使
$$
zv=0\ (v\in V),\qquad \|z\|_1=1,\qquad zh=d.
\tag{15.12}
$$
此处使用的是成熟的商范数对偶，见 Walter Rudin，*Functional Analysis*，第二版（1991），第3章的 Hahn–Banach 延拓与分离定理；式（15.12）亦由将上述商泛函拉回原空间直接得到。因为 $z\mathbf1=0$，其正、负部分的质量同为 $1/2$。故 $p=2z^+$、$q=2z^-$ 是概率分布，$pB=qB$，而 $ph-qh=2d$。任意解码器在同一个预测值上只给一个实数 $c$；由 $|ph-qh|\le|ph-c|+|qh-c|$，至少一个误差不小于 $d$。这与上界吻合。零先验坐标不需条件化，因而边界分布同样是合法下界见证。$\square$

**定理 15.6（预测多面体的正实现与全制备域下界）。** 设 $v_1,\ldots,v_k$ 是 $\mathcal P$ 的全部不同顶点。存在一个 $k$ 隐状态、动作集 $A$、输出集 $Y$ 的非负联合仪器，其全概率单纯形的预测像恰为 $\mathcal P$，且对每个 $s\in\mathcal P$ 保留全部受控词概率及允许的自适应记录律。

比较另一 $N$ 隐状态仪器时，要求每个 $\lambda\in\Delta_N$ 都是允许制备，并且在同一词概率识别下，其整个 $\Delta_N$ 的预测像恰好等于 $\mathcal P$。在这些量词下必有 $N\ge k$，所以前述构造最小。该下界不适用于只准许单纯形的一个子集、允许更大预测域或只指定一个初始制备的竞争问题。正实现的隐状态数也不是确定性观察者可取的预测态数：[量子算术卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)§151—155已经分别研究有限隐状态生成、无限精确预测商及有限精度历史记忆。

**证明。** 固定 $i,a,y$。定理15.3使 $v_iM_{a,y}\in\mathcal C$，质量 $\ell_i=v_iM_{a,y}e_1\ge0$。若 $\ell_i>0$，其归一化位于 $\mathcal P$，故可选顶点分解
$$
\frac{v_iM_{a,y}}{\ell_i}=\sum_j\alpha_{i,a,y,j}v_j,\qquad
\alpha_{i,a,y,j}\ge0,\qquad\sum_j\alpha_{i,a,y,j}=1.
$$
置 $\widehat K_{a,y}(i,j)=\ell_i\alpha_{i,a,y,j}$。若 $\ell_i=0$，则未归一化向量为零，将该分支整行置零。于是 $\widehat K$ 非负，且对每个 $i,a$ 有 $\sum_{y,j}\widehat K_{a,y}(i,j)=1$。令 $R$ 的第 $i$ 行为 $v_i$，便有
$$
\widehat K_{a,y}R=RM_{a,y},\qquad Re_1=\mathbf1.
\tag{15.13}
$$
对任意分解 $s=\lambda R$、$\lambda\in\Delta_k$，逐词相乘得
$$
\lambda\widehat K_w\mathbf1=sM_we_1.
$$
因而每个分解都给相同测试律，式（15.9）的自适应等价给完整实验结论。其全制备像为全部顶点的凸包，恰是 $\mathcal P$。

对竞争实现，令 $t_i\in\mathcal P$ 为第 $i$ 个纯态的预测像。测试概率对初始混合是仿射的，而它们识别 $s$，故整个单纯形的像为 $\operatorname{conv}\{t_1,\ldots,t_N\}=\mathcal P$。任一顶点 $v$ 写成这些 $t_i$ 的凸组合时，极端性迫使所有正权重项都等于 $v$；于是每个不同顶点必须由至少一个纯态给出，$N\ge k$。分解系数无须唯一，证明只给存在的正实现，不给免费、唯一的隐态解码器，也不把混合分布当作已取得的隐态样本。

受限制备确实改变结论。取 $\Delta_3$ 中的六边形 $D=\{p:p_i\le2/3\}$；其顶点是 $(2/3,1/3,0)$ 的六个排列：在平面 $\sum_ip_i=1$ 内，顶点至少有两个独立的坐标边界约束；两个零或两个 $2/3$ 都不满足总和条件，故只能一个零、一个 $2/3$、另一个 $1/3$，而这六个点确实各由两个边界唯一确定。三个隐状态、唯一动作读取状态符号 $i\in\{1,2,3\}$ 后重置到均匀律，则初始 $p$ 的未来是首符号服从 $p$、以后独立均匀。只准许 $p\in D$ 时，其预测域有六顶点却只用三个隐状态，且重置均匀律仍属 $D$。同一预测域也可由六态全制备实现：第 $i$ 态按第 $i$ 个顶点的三符号概率输出，再独立重置到六态均匀律。六顶点的平均是三符号均匀律，故全部后续词匹配。三态系统被排除的纯制备恰在 $D$ 外，因此没有违反全单纯形下界。$\square$

**命题 15.7（正方形预测域与不能恢复的交互目标）。** 取 $X=\{00,01,10,11\}$，$A=\{1,2\}$，$Y=\{0,1\}$。动作 $i$ 读出当前第 $i$ 位后重置为 $00$，即
$$
K_{i,y}(x,x')=\mathbf1_{\{x_i=y\}}\mathbf1_{\{x'=00\}}.
\tag{15.14}
$$
则 $V=\operatorname{span}\{\mathbf1,x_1,x_2\}$，齐次线性维数 $r=3$，$\mathcal P=\{(1,u,v):0\le u,v\le1\}$ 有四顶点。在定理15.6的全制备、精确相同预测域量词下，正实现恰需四个隐状态。初始交互目标 $h=x_1x_2$ 不能精确恢复，其最小最坏误差为 $1/4$。

**证明。** 一步词列为 $x_i$ 或 $1-x_i$。读出后已是 $00$，所有后续输出均为零，所以非空词列或为上述一步词列，或为零；连同空词，恰张成所述三维空间。以 $B=(\mathbf1,x_1,x_2)$ 为基，四行就是正方形四顶点，因此两种维数与顶点结论分别来自定理15.4和15.6。相应四个 $M_{i,y}$ 除第一列外全为零，其第一列依次为
$$
M_{1,0}e_1=(1,-1,0)^{\mathsf T},\quad
M_{1,1}e_1=(0,1,0)^{\mathsf T},\quad
M_{2,0}e_1=(1,0,-1)^{\mathsf T},\quad
M_{2,1}e_1=(0,0,1)^{\mathsf T}.
\tag{15.15}
$$
故分支质量为 $1-u,u,1-v,v$，每个正质量分支都更新为 $(1,0,0)$；零质量分支没有后验。这里的负元素已在实际域上给合法概率，无须另换基。

令 $p_{\rm even}$ 在 $00,11$ 上各取 $1/2$，$p_{\rm odd}$ 在 $01,10$ 上各取 $1/2$。它们均给 $s=(1,1/2,1/2)$，但 $p_{\rm even}h=1/2$、$p_{\rm odd}h=0$，故任意解码器的最坏误差至少 $1/4$。列函数
$$
v_*=(x_1+x_2)/2-1/4
$$
在四点上与 $h$ 的差依次为 $1/4,-1/4,-1/4,1/4$，给上界 $1/4$，并具体实现定理15.5。两个同边缘先验的全部允许未来词律已相同；要取得区分它们的新数据，必须扩充原先声明的动作或测试语言，不能仅重新计算 $s$。$\square$

**命题 15.8（当前预测商不恢复来源档案）。** 在命题15.7的同一仪器中，设初始位对为 $(\Theta,0)$，$\Theta$ 公平，$C$ 可包含任何已取得旧记录。先执行动作1并保留输出。两个正概率历史 $H_1=(C,1,0)$、$H_1=(C,1,1)$ 在共同 $C$ 的正概率纤维上均可出现时，它们的当前预测态同为 $(1,0,0)$，全部环境未来输出都为零，但来源后验分别为 $\Theta=0$、$\Theta=1$ 的点质量。

**证明。** 动作1输出初始 $\Theta$，随后两支均重置为 $00$，故当前律与未来预测相同，而保留的输出精确决定来源。条件为两支正概率；若 $C$ 已决定 $\Theta$，就在相应纤维只保留有支撑的一支，不制造另一支条件律。因此 $s$ 不能重建完整 $H_1$ 或来源后验。若控制器以后根据旧输出选择动作，两个历史还可产生不同的动作记录；定理15.4的反馈比较要求相同的初始控制器访问情境，不能用环境预测相同删除这项要求。[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§38.1—38.2已区分任务摘要、合法动作与旧档案的在线取得；本例给出其与状态重置的连接。$\square$

## 16. 固定动作词与反馈实验的同核异距

**定义 16.1（共同仪器的有限时域距离）。** 固定约定15.1的同一有限仪器、同一个确定的初始可访问记录 $H_0=c$ 及相同控制器初始状态。两个先验 $p,q\in\Delta_X$ 只改变隐藏初态律，不改变策略、动作访问权或核。对整数 $H\ge1$，定义
$$
\begin{aligned}
d_{{\rm ol},H}(p,q)
&=\max_{\boldsymbol a\in A^H}
\operatorname{TV}(P_p^{\boldsymbol a},P_q^{\boldsymbol a}),\\
d_{{\rm fb},H}(p,q)
&=\sup_{\pi}
\operatorname{TV}(P_p^{\pi,H},P_q^{\pi,H}),\qquad
\operatorname{TV}(P,Q)=\tfrac12\sum_z|P(z)-Q(z)|.
\end{aligned}
\tag{16.1}
$$
前者的随机对象是整个输出词；后者为整个动作—输出记录，$\pi$ 遍历满足式（15.3）的共同历史反馈策略。固定词实验的动作是确定的，将它附在输出词上不改变 TV。外部随机策略种子独立于隐藏初态及环境噪声；所比较的双方使用同一策略机制，条件核契约仍须成立。定义 $d_{{\rm ol},0}=d_{{\rm fb},0}=0$，因为初始可访问记录已固定相同。随机终止若纳入模型，完整记录用共同吸收符号延长到 $H$。

**定理 16.2（有限时域比较界）。** 令 $m=|A|\ge1$。定义16.1的两个量是 $\Delta_X$ 上的伪度量，并满足
$$
d_{{\rm ol},H}\le d_{{\rm fb},H}
\le\min\{1,m^{H-1}d_{{\rm ol},H}\}\qquad(H\ge1).
\tag{16.2}
$$
对单个确定性策略树 $\pi$，可将右侧因子换成 $N_\pi$：它是在 $p$ 或 $q$ 的记录支撑上出现的不同完整动作词数，$1\le N_\pi\le m^{H-1}$。随机策略的统一结论使用 $m^{H-1}$，不把不同确定性树的词数未经控制地合成一个更小因子。$H=1$ 或 $m=1$ 时两个距离相等。

**证明。** 每个固定实验的 TV 满足非负性、对称性、对角为零和三角不等式；在同一个预先固定的实验族上取上确界仍有这些性质。这是[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§17.4—17.5的一般行为伪度量方法在有限 $H$ 上的直接应用。固定动作词属于反馈策略族，给左侧界，TV 本身给上界一。

先取确定性策略树。初始记录相同且固定，所以首动作固定。将全部可能记录按其完整动作词 $\boldsymbol a$ 分组；对每组令 $E_{\boldsymbol a}\subseteq Y^H$ 为沿该输出词恰使策略选择 $\boldsymbol a$ 的输出集合。这个相容性集合由同一策略决定，与 $p,q$ 无关。由式（15.3），在相容记录上策略概率因子全为一，因此
$$
\begin{aligned}
\operatorname{TV}(P_p^{\pi,H},P_q^{\pi,H})
&=\frac12\sum_{\boldsymbol a}
\sum_{\boldsymbol y\in E_{\boldsymbol a}}
\left|pK_{a_1,y_1}\cdots K_{a_H,y_H}\mathbf1
-qK_{a_1,y_1}\cdots K_{a_H,y_H}\mathbf1\right|\\
&\le\sum_{\boldsymbol a\ {\rm realized}}
\operatorname{TV}(P_p^{\boldsymbol a},P_q^{\boldsymbol a})
\le N_\pi d_{{\rm ol},H}(p,q).
\end{aligned}
\tag{16.3}
$$
任一方支撑均为空的组贡献零，可以删去；其余组的受限非负绝对值和至多为全输出词之和。首动作固定，剩余 $H-1$ 个动作每步至多 $m$ 种，故 $N_\pi\le m^{H-1}$。

有限时域、有限动作输出下，行为随机策略可在开始前对每个可能历史节点独立抽取其动作，把它写成有限个确定性策略树的混合。混合权重只依赖策略核，与隐藏初态及环境噪声独立，并在两侧相同。一般独立随机种子的策略也可先固定种子而得到确定性树，再按树合并权重。TV 的凸性使每个分量的统一 $m^{H-1}$ 界在混合后仍成立。若独立种子也写入被比较的记录，按该种子分层计算 TV 是分量 TV 的平均，同一界仍有效；没有把种子当成隐藏状态的额外观测。最后取策略上确界得式（16.2）。$H=1$ 或 $m=1$ 时因子为一，与左界夹合；$H=0$ 按定义另行取零，无需解释负指数。

固定 $c$ 是该计数证明的条件。如果未条件化的随机旧档案已经能选择首动作，就不能直接套用“首动作固定”的 $m^{H-1}$ 论证；应在共同正概率档案纤维上比较，或为所使用的初始记录实验族另立界。$\square$

**定理 16.3（随时域变化的锐挑战仪器）。** 对每个 $m\ge2,H\ge2$，存在满足约定15.1的有限、时间齐次仪器及两个具有相同初始可访问记录的初态 $p,q$，使
$$
d_{{\rm ol},H}(p,q)=m^{-(H-1)},\qquad
d_{{\rm fb},H}(p,q)=1.
\tag{16.4}
$$
所有动作均合法，失败完整保留。这给出式（16.2）指数因子的锐例族；它排除跨全部有限模型及全部时域的统一常数，而不声称某一个固定模型在任意大 $H$ 都有该精确比值。

**证明。** 令 $A=\{1,\ldots,m\}$，初态为携带隐藏位 $z\in\{0,1\}$ 的 $S_z$，$p=\delta_{S_0}$、$q=\delta_{S_1}$。输出字母为互不混淆的挑战符号 $c_r$、最终位符号 $b_0,b_1$、失败符号 $\dagger$ 与完成后符号 $*$。从 $S_z$ 执行任意动作，都均匀输出 $c_{r_1}$，并进入状态 $(z,2,r_1)$。一般待执行阶段状态 $(z,t,r)$ 满足 $2\le t\le H$：若动作 $a\ne r$，输出 $\dagger$ 并进入失败吸收态；若 $a=r$ 且 $t<H$，独立均匀生成新挑战 $r'$，输出 $c_{r'}$ 并进入 $(z,t+1,r')$；若 $a=r$ 且 $t=H$，输出 $b_z$ 并进入完成吸收态。失败态永远输出 $\dagger$，完成态永远输出 $*$，两者对所有动作均保持自身。把阶段计数纳入有限状态后，这是一套时间齐次、逐行动总质量为一的非负联合核。

固定动作词 $(a_1,\ldots,a_H)$。到达最终位输出当且仅当每个 $r_{t-1}=a_t$，$2\le t\le H$，其概率为
$$
\alpha=m^{-(H-1)}.
$$
第一次动作不影响挑战律。可以事先生成独立公平挑战序列，在两种 $z$ 下共用它；每个失败记录的概率由挑战和动作决定，与 $z$ 无关。成功记录则在最终位符号上分别为 $b_0,b_1$，两个成功部分支撑不交，各有质量 $\alpha$。故半 $\ell_1$ 差恰为 $\alpha$，对每个固定动作词都相同。

反馈策略任取首动作，以后总选择刚读到的挑战值。每步匹配，因此成功概率为一，最后必读到 $b_z$；两种初态的完整记录支撑不交，TV 为一。保留失败记录是固定词 TV 计算的一部分，没有通过条件成功后丢弃概率质量来放大距离。每个 $H$ 的阶段状态集合不同，正说明此处量词是一个模型族。$\square$

**命题 16.4（同一锐例中的固定来源创新）。** 在定理16.3的仪器中，把隐藏初始位作为固定来源目标 $Z\sim\operatorname{Bernoulli}(1/2)$，初始档案常值。固定动作词的总均方创新及末端 Bayes 风险分别为
$$
I_{\rm ol}=\frac{\alpha}{4},\qquad
R_{\rm ol}=\frac{1-\alpha}{4},\qquad\alpha=m^{-(H-1)}.
\tag{16.5}
$$
匹配挑战的反馈策略对应 $I_{\rm fb}=1/4$、$R_{\rm fb}=0$。这里总创新指
$\mathbb E[(\mathbb E[Z\mid H_H]-1/2)^2]$。

**证明。** 在任一挑战前缀及每个失败记录上，$Z$ 的条件律仍为公平位，因为该记录只由独立挑战与已指定动作生成。固定词成功时才观察 $b_Z$，随后后验为点质量。因此末端条件均值在失败时为 $1/2$，在成功时为 $Z$；均方创新为 $\alpha(1/2)^2$。末端条件方差在失败时为 $1/4$，在成功时为零，积分给风险式。反馈匹配必然成功，所以获得全部初始 $1/4$ 风险预算。第17节的固定目标塔公式将把总创新分成实际各步之和。两种策略分别诱导不同的完整联合律；策略计算只选择了更有效的取得路径，并没有无输入地创造来源信息。$\square$

**推论 16.5（精确商相同不等于统一的稳定性常数）。** 对定义16.1的每个有限 $H$，$d_{{\rm ol},H}$ 与 $d_{{\rm fb},H}$ 有同一零核；在所有有限 $H$ 上同时取零，恰得到定理15.4的预测商。但若只给一个 $H$ 步开环误差预算，转为该时域反馈误差的统一乘法常数不能小于定理16.3例族的 $m^{H-1}$。

**证明。** 有限正因子的双边界（16.2）给同零核，遍历全部 $H$ 即为全部词的相等关系。把定理16.3的两个数代入任何候选乘法界 $d_{{\rm fb},H}\le c\,d_{{\rm ol},H}$，得到 $c\ge m^{H-1}$。因此在同一个语义商上，允许实验族仍决定误差几何。

[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理21.6从全状态、全动作的输出—后继摘要联合核缺陷得到完整记录界 $1-(1-\varepsilon)^H\le H\varepsilon$；它的前提比这里只约束固定词记录的前提不同，本锐例不反驳该逐步联合证书。若比较两套模型，可用带不变模型标签的互不相交状态并集、块对角共同仪器及同一动作输出字母表，将比较写成一套源模型上的两个先验；已有档案、失败语义与策略访问权仍须对齐。该构造直接保留两套联合核，并不允许把独立取得的边缘读数拼成共同实现。$\square$

## 17. 固定来源目标的动作依赖创新与联合记忆

**定义 17.1（完整历史上的来源后验与有效似然）。** 固定有限非空来源标签集 $\Theta$、有限当前状态集 $X$、有限非空动作与输出集、有限的已表示旧档案字母集，以及有限时域 $T\ge0$。$\Theta$ 表示同一个固定来源目标，例如初始状态的标签；隐藏当前状态 $X_t$ 可以被动作和输出共同改变。以 $H_0=C$ 开始，$C$ 包括全部已表示的来源记录、内外档案及控制器初始可访问关系；以后 $H_{t+1}=(H_t,A_t,Y_{t+1})$ 保留旧历史。给定允许策略及受控模型，得到一份完整联合律。对正概率条件事件采用顺序生成契约
$$
\Pr(A_t=a,Y_{t+1}=y,X_{t+1}=x'\mid
\Theta=\theta,X_t=x,H_t=h)
=\pi_t(a\mid h)T_t(x',y\mid\theta,x,h,a),
\tag{17.1}
$$
其中 $T_t$ 是逐输入归一化的非负核；给定更早隐藏路径也使用此核。$\pi_t$ 只能访问实际 $h$ 及允许的独立随机源，不直接访问 $\theta,x$。动作守卫若存在，$\pi_t$ 支撑于已声明的合法动作。这个[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定义17.1型条件因子化，比仅说“开始时抽了一枚独立种子”更具体。

在 $\Pr(H_t=h)>0$ 时令 $b_h(\theta)=\Pr(\Theta=\theta\mid h)$，以下把 $b_h$ 写成概率列向量。对 $\pi_t(a\mid h)>0$ 的动作，及 $b_h(\theta)>0$ 的来源类，定义
$$
\begin{aligned}
\mu_h(\theta,x)&=\Pr(\Theta=\theta,X_t=x\mid h),\\
L_{h,a}(y\mid\theta)
&=\sum_x\frac{\mu_h(\theta,x)}{b_h(\theta)}
\sum_{x'}T_t(x',y\mid\theta,x,h,a).
\end{aligned}
\tag{17.2}
$$
它是从完整受控联合律导出的有效似然。$b_h(\theta)=0$ 时可给 $L_{h,a}(\cdot\mid\theta)$ 任意概率行，其后总被零质量乘掉；$h$ 无支撑时不定义其后验。未被该策略选择的合法动作若要参与比较，须有已指定的干预核 $T_t$，再用式（17.2）定义相应实验，不能把零概率条件事件当作实际观测。

仅给 $b_h$ 不保证能得到式（17.2）：同来源条件下的当前状态律、历史依赖核及动作守卫均可能仍缺失。若要闭合递推，须增加任务实际需要的联合状态或历史关系。[AdaptivePosteriorPolicySufficiency](../../../D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency.lean)要求共同来源条件实验核及正确 Bayes 历史扩展；它不把这些前提从来源边缘后验中自动导出。本节讨论概率、投影和固定目标风险，不从“状态”“空间”“时间”或“创新”的名称推出物理波、场或衰变定律。

**命题 17.2（动作选择本身的来源零创新）。** 在定义17.1的正概率历史 $h$ 及被选择概率为正的动作 $a$ 上，
$$
\Pr(\Theta=\theta\mid H_t=h,A_t=a)=b_h(\theta).
\tag{17.3}
$$
确定性动作可测于 $H_t$，不增加其 $\sigma$ 代数；随机动作虽可增加记录的 $\sigma$ 代数，却在式（17.1）下不改变来源后验。该结论不适用于与隐藏来源相关而未满足此条件因子化的随机化。

**证明。** 将式（17.1）对 $x',y$ 求和，并按 $\mu_h(\theta,x)$ 对 $x$ 积分，得到
$$
\Pr(\Theta=\theta,A_t=a\mid h)=b_h(\theta)\pi_t(a\mid h).
$$
除以正数 $\pi_t(a\mid h)$ 给式（17.3），即条件独立。确定性时 $A_t=\pi_t(h)$ 直接为历史函数。若反而让动作取未被历史揭示的来源位 $A_t=\Theta$，公平来源、常值历史下动作就揭示来源，明确违反上述因子化，因而不是本命题的反例。$\square$

**定理 17.3（单步来源创新协方差与剩余预算）。** 固定定义17.1的正概率 $h,a$，记 $b=b_h$、$L=L_{h,a}$，并置
$$
q_y(\theta)=b(\theta)L(y\mid\theta),\qquad
p_y=\sum_\theta q_y(\theta),\qquad
b_y=q_y/p_y\quad(p_y>0).
\tag{17.4}
$$
则 $\sum_yq_y=b$、$\sum_yp_y=1$，正质量时 $b_y$ 是给定新动作与输出后的来源后验。定义
$$
\begin{aligned}
G(h,a)
&=\sum_{y:p_y>0}\frac{q_yq_y^{\mathsf T}}{p_y}-bb^{\mathsf T}\\
&=\sum_{y:p_y>0}p_y(b_y-b)(b_y-b)^{\mathsf T}.
\end{aligned}
\tag{17.5}
$$
有
$$
0\preceq G(h,a)\preceq\operatorname{Diag}(b)-bb^{\mathsf T},\qquad
G(h,a)\mathbf1=0,
\tag{17.6}
$$
以及精确预算恒等式
$$
\operatorname{Diag}(b)-bb^{\mathsf T}
=G(h,a)+\sum_{y:p_y>0}p_y
\bigl[\operatorname{Diag}(b_y)-b_yb_y^{\mathsf T}\bigr].
\tag{17.7}
$$

**证明。** 似然每行和为一，故对 $y$ 求和给 $b$，再对来源求和给一。命题17.2使选择动作前后的 $b$ 相同，随后 Bayes 公式给式（17.4）。$p_y=0$ 时非负向量 $q_y$ 必为零；不定义 $b_y$，该项从全部和中删去。展开式（17.5）第二行，并使用 $\sum_{p_y>0}p_yb_y=b$，得到第一行。

每个外积 $(b_y-b)(b_y-b)^{\mathsf T}$ 半正定，故 $G\succeq0$；且 $(b_y-b)^{\mathsf T}\mathbf1=0$，给 $G\mathbf1=0$。任意概率列 $u$ 满足
$$
v^{\mathsf T}[\operatorname{Diag}(u)-uu^{\mathsf T}]v
=\sum_\theta u_\theta(v_\theta-u^{\mathsf T}v)^2\ge0
$$
对每个实列 $v$ 成立。最后 $\sum_yp_y\operatorname{Diag}(b_y)=\operatorname{Diag}(b)$，而 $\sum_yp_yb_yb_y^{\mathsf T}=G+bb^{\mathsf T}$，相减即式（17.7）；余项半正定给上界。若来源支撑为单点，左侧为零，必有 $G=0$；若某个来源质量为零，其在所有正质量后验中也为零，对应行列均不贡献。

这是来源指标向量 $\mathbf e_\Theta$ 的全协方差公式：总条件协方差等于条件均值的协方差加平均剩余协方差。所用条件期望及塔式恒等式是成熟概率论，见 David Williams，*Probability with Martingales*（1991），第9章；这里已用有限求和完整展开。它是本卷命题14.3的固定律嵌套投影在来源指标函数上的矩阵形式，不要求读数之间独立。$\square$

**定理 17.4（固定目标的风险下降与实际策略总创新）。** 在定义17.1的一份实际联合律下，给定固定函数 $f:\Theta\to\mathbb R$，将其值列记为 $f$。对每个正概率 $h,a$，一次观测的条件 Bayes 均方风险下降等于
$$
\operatorname{Var}(f(\Theta)\mid h)
-\sum_{y:p_y>0}p_y\operatorname{Var}(f(\Theta)\mid h,a,y)
=f^{\mathsf T}G(h,a)f.
\tag{17.8}
$$
令 $m_t=\mathbb E[f(\Theta)\mid H_t]$。则
$$
\begin{aligned}
\sum_{t=0}^{T-1}\mathbb E[f^{\mathsf T}G(H_t,A_t)f]
&=\sum_{t=0}^{T-1}\mathbb E[(m_{t+1}-m_t)^2]\\
&=\mathbb E[(m_T-m_0)^2]\\
&=\mathbb E[\operatorname{Var}(f(\Theta)\mid C)]
-\mathbb E[\operatorname{Var}(f(\Theta)\mid H_T)]\\
&\le\mathbb E[\operatorname{Var}(f(\Theta)\mid C)].
\end{aligned}
\tag{17.9}
$$
各期望只在其实际历史和动作支撑上求和。停止后的吸收延续不增加来源信息时，其创新为零。$T=0$ 时空和及风险差均为零。

**证明。** 用 $f$ 左右乘式（17.7），各协方差二次型正是相应条件方差，得式（17.8）。也可在每个后验下展开平方损失：对任意实数 $d$，
$$
\mathbb E[(f(\Theta)-d)^2\mid h]
=\operatorname{Var}(f(\Theta)\mid h)+(b_h^{\mathsf T}f-d)^2,
$$
故条件均值为 Bayes 解。命题17.2使给定 $H_t,A_t$ 的观测前条件均值仍为 $m_t$，式（17.5）遂给
$\mathbb E[(m_{t+1}-m_t)^2\mid H_t,A_t]=f^{\mathsf T}G(H_t,A_t)f$。

历史保留使各 $\sigma(H_t)$ 嵌套，同一固定目标的 $m_t$ 为鞅。对于 $i<j$，$m_{i+1}-m_i$ 在 $H_j$ 下可测，而 $\mathbb E[m_{j+1}-m_j\mid H_j]=0$，所以两增量的内积期望为零。正交增量求和得式（17.9）的第二行；把单步风险差积分后望远镜求和得第三行，末端风险非负给最后界。本卷命题14.3、[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)§121及[ConditionalExpectationRefinementPythagoras](../../../D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras.lean)已给嵌套条件期望的同一 Pythagoras 供应结构；本式将其落实到受控历史上的 $G(H_t,A_t)$。

此处非负的是对下一观测平均后的风险下降，不声称每个分支的条件方差都下降。例如 $\Theta\sim\operatorname{Bernoulli}(1/10)$，取二元输出满足 $L(1\mid1)=1$、$L(1\mid0)=1/9$。则 $p_1=1/5$，该支后验公平，方差 $1/4$ 大于先验方差 $9/100$；另一支后验为零态，平均剩余风险为 $1/20$，总下降 $1/25>0$。不同策略产生不同联合律，各自按式（17.9）结算，不把分别可达的逐步最大创新当作同一策略的同时收益。$\square$

**命题 17.5（移动当前目标不满足固定目标望远镜式）。** 即使全部输出无信息，$f(X_t)$ 的当前状态风险也可随状态扰动增加，因此不能将式（17.9）的 $f(\Theta)$ 直接替换为每步变化的 $f(X_t)$。

**证明。** 取 $X=\{0,1\}$、唯一动作、唯一输出 $*$，仪器从任一状态以概率各 $1/2$ 转到 $0,1$ 并输出 $*$。初态确定为 $X_0=0$，档案常值，令 $f(x)=x$。初始目标 $f(X_0)$ 的风险为零；一步后 $X_1$ 为不可见公平位，所以当前目标 $f(X_1)$ 的风险为 $1/4$，历史观测没有增加信息。若对每时刻当前目标错误使用固定目标风险差，就得到 $-1/4$，无法等于非负创新。真正固定的来源 $\Theta=X_0$ 始终确定，其来源创新和风险均为零，完全符合式（17.9）。改变被预测随机变量引入预测漂移；这一差异是目标定义的变化，不是任何物理熵定律的推论。$\square$

**命题 17.6（自适应读取混合既有交互扇区）。** 在均匀四点空间上取独立 $U,V\in\{-1,1\}$，旧档案常值，动作均为不扰动读取。先读 $U$，仅当 $U=1$ 时读 $V$，否则停止，并把停止及已读内容保留为记录 $H$。令 $P_H=\mathbb E[\cdot\mid H]$，$D_V$ 为原固定乘积空间中投影到 $\operatorname{span}\{V\}$ 的 Walsh 扇区投影，则
$$
P_HV=\mathbf1_{\{U=1\}}V=\frac{V+UV}{2},\qquad
D_VP_HV=\frac V2\ne\frac{V+UV}{2}=P_HD_VV.
\tag{17.10}
$$
因此 $P_H$ 不是第14节那些固定 $D_S$ 的某个子族之和；实际嵌套历史仍有正交创新。

**证明。** $U=1$ 时记录包含 $V$，条件均值为 $V$；$U=-1$ 时两种 $V$ 仍等概率，条件均值为零。独立公平位的 $1,U,V,UV$ 是正交归一基，故投影到 $V$ 扇区只保留 $(V+UV)/2$ 的 $V/2$ 部分，得到不交换式。任何固定正交 $D_S$ 的和都与每个 $D_S$ 交换，因而不能等于 $P_H$。具体地，$P_HV$ 的平方范数为 $1/2$，其旧扇区 $V$、$UV$ 分量的平方范数各为 $1/4$。从常值记录到读 $U$ 再到 $H$ 的投影仍嵌套，定理17.4或命题14.3给正交增量；改变的是“某个旧扇区在固定时刻完整显露”的解释条件。此例没有扰动，已经越出定理14.10的事先固定全枚举前提。$\square$

**定理 17.7（保留来源标记的有限预测接口）。** 对约定15.1的共同有限仪器，进一步要求未来核给定当前 $X_t$ 后不直接依赖来源 $\Theta$ 或历史，且来源标签自身不变。令 $B,M_{a,y}$ 如定理15.3。对任意正概率历史 $h$ 的联合后验 $\mu_h(\theta,x)$，定义行按来源排列的矩阵
$$
J_h(\theta,:)=\mu_h(\theta,:)B.
\tag{17.11}
$$
则来源边缘、当前环境预测态及来源标记词概率分别为
$$
b_h=J_he_1,\qquad
s_h=\sum_\theta J_h(\theta,:),\qquad
\Pr(\Theta=\theta,\text{输出词 }\boldsymbol y
\mid h,\text{执行固定动作词 }\boldsymbol a)
=J_h(\theta,:)M_we_1.
\tag{17.12}
$$
这里的“执行固定动作词”表示指定干预实验，并非对一个反馈策略末端动作词的事后条件化。对已选择动作 $a$ 的输出分支，总质量
$$
\ell=\sum_\theta J_h(\theta,:)M_{a,y}e_1
$$
为正时，联合预测接口更新为
$$
J_{hay}=\frac{J_hM_{a,y}}{\ell}.
\tag{17.13}
$$
零质量分支没有条件接口。两个联合后验的 $J$ 相等，当且仅当全部来源标记有限词概率相等，包括空词的来源质量；在相同初始可访问记录和同一策略契约下，还保留全部来源—自适应完整记录联合律。

**证明。** 对 $\mu_h$ 的每个来源行应用 $Be_1=\mathbf1$，得来源边缘；对来源行求和得当前状态边缘的 $B$ 读出。固定来源标签不变、仪器在给定 $X_t$ 后共同，故来源标记词概率为 $\mu_h(\theta,:)K_w\mathbf1$。由 $K_wB=BM_w$ 得式（17.12）。式（15.3）使选择动作的因子与 $\theta,x$ 无关；选择动作后联合后验仍为 $\mu_h$，而观察输出后变为
$$
\mu_{hay}(\theta,:)=\mu_h(\theta,:)K_{a,y}/\ell.
$$
右乘 $B$ 得更新式。质量为零时各来源行对应的非负输出质量都为零，无须也不能除以零。若 $b_h(\theta)=0$，则 $\mu_h(\theta,:)=0$、$J_h(\theta,:)=0$；其全部标记词概率为零。

$J$ 相等显然给所有标记词概率相等。反向，逐来源行的联合后验差消去全部 $K_w\mathbf1$，由它们张成 $V$，该行乘 $B$ 为零；逐行即得 $J$ 相等。对任一来源标记的完整自适应记录，用共同记录策略乘子乘式（17.12），再按[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理17.2的同一逐记录论证，得联合律相等。与[PredictiveStateUnifilarUpdate](../../../D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean)相同，条件递推仅在正质量分支上由未来律唯一确定。

给定 $J_h$ 后，单步 $q_y$ 的来源分量就是 $J_h(\theta,:)M_{a,y}e_1$，所以式（17.5）的 $G(h,a)$ 也能计算。该接口保留任务可见的来源—未来关系，而删去逐来源行中消去 $V$ 的隐藏坐标；完整微观联合后验是一种充分表示，不因此成为必要表示。例如定理15.7的同预测先验分别配置在相同来源行上，便可有不同微观后验而同 $J$。这里没有宣称任意编码的实坐标或位数最小性。

若核直接依赖 $\Theta$，应将来源并入被声明的状态或采用相容的来源专属张成及矩阵；若核直接依赖历史，还须加入使核闭合的历史状态，且有限性须另证。未完成这些补充时，不能沿用一个共同 $M$。$J_h$ 也不代替已取得的 $C$ 或控制器需要的旧档案；未来来源标记概率的相等只针对声明的实验语言。$\square$

**命题 17.8（同一模型中相同来源边缘与预测边缘仍有不同创新）。** 存在一个有限、唯一动作的受控模型，两条正概率历史具有相同来源后验、相同当前状态预测态和全部环境未来输出律，却对下一读数给不同的 $G$。因此 $(b_h,s_h)$ 一般不能替代来源标记接口 $J_h$。

**证明。** 令来源 $\Theta$ 公平。隐藏状态有初始态 $S_0,S_1$、就绪态 $R_0,R_1$ 及重置态 $O$，初态为 $S_\Theta$；来源标签固定保留在联合律中。首步输出独立公平模式位 $R$：当 $R=0$ 时转到 $R_\Theta$，当 $R=1$ 时另抽独立公平位 $Z$ 并转到 $R_Z$。明确地，从 $S_\theta$ 到输出模式0、就绪态 $R_\theta$ 的概率为 $1/2$；到输出模式1、任一就绪态 $R_z$ 的概率各为 $1/4$。从 $R_z$ 下一步输出读数位 $z$ 并转到 $O$；$O$ 此后恒输出共同吸收符号。模式输出与读数输出采用不同标签，状态内阶段使这是一套时间齐次仪器。

两个正概率历史 $h_0=(C,R=0)$、$h_1=(C,R=1)$ 的概率各为 $1/2$，$C$ 常值。因为模式独立，两个来源后验均为 $(1/2,1/2)^{\mathsf T}$。在两支下就绪位边缘均公平，所以当前状态律均在 $R_0,R_1$ 上各半，未来都先读一个公平位再吸收，预测态相同。但 $h_0$ 下读数位等于来源，$h_1$ 下读数位独立于来源，因此
$$
G(h_0,a)=\frac14
\begin{pmatrix}1&-1\\-1&1\end{pmatrix},\qquad
G(h_1,a)=0.
\tag{17.14}
$$
第一式因两个后验分别为来源点质量而来自式（17.5），第二式因每个后验都仍为公平来源。对 $f(\theta)=\theta$，创新分别为 $1/4$ 与零。来源标记下一读数的联合律分别是对角的两点各半与四点各 $1/4$，所以定理17.7的 $J$ 必然不同。两个档案中的模式记录确实不同并被保留；例子正是说明省略它及其所决定的联合关系会丢失来源创新信息，不把这两个历史冒充相同访问记录。命题15.8另显示重置可使当前预测完全相同，而档案仍保留不同来源事实。$\square$

**定理 17.9（完整来源—记录联合误差控制总创新）。** 在同一有限字母空间上给两个概率律 $P_{\Theta,H},Q_{\Theta,H}$；记录通过同一个映射 $C=c(H)$ 保留旧档案。假设两律的 $(\Theta,C)$ 边缘相同。给固定 $f:\Theta\to[m_f,M_f]$，$D=M_f-m_f\ge0$，记
$$
\delta=\operatorname{TV}(P_{\Theta,H},Q_{\Theta,H}),\qquad
m_C=\mathbb E[f(\Theta)\mid C]
$$
为共同初始条件均值，并定义
$$
I(P)=\mathbb E_P[(\mathbb E_P[f(\Theta)\mid H]-m_C)^2],
\qquad I(Q)\text{ 同理}.
\tag{17.15}
$$
则
$$
|I(P)-I(Q)|\le D^2\delta.
\tag{17.16}
$$
常数一不能统一缩小。这里只需完整联合律的 TV，不需要逐历史的后验误差界。

**证明。** 由 $C$ 被 $H$ 保留，在每份律中对固定目标应用嵌套投影，得
$$
I(P)=R_C-R(P),\qquad
R(P)=\inf_g\mathbb E_P[(f(\Theta)-g(H))^2],
\tag{17.17}
$$
其中 $R_C=\mathbb E[(f(\Theta)-m_C)^2]$ 由共同 $(\Theta,C)$ 边缘决定，$Q$ 亦同。把任何 $g$ 裁剪到 $[m_f,M_f]$ 只会逐点减小平方损失，故两个下确界都可取同一个有界解码器类。零概率历史上任选此区间中的值即可，不影响相应期望；有限支撑使条件均值达到最小值。

对每个这样的 $g$，损失 $\ell_g(\theta,h)=(f(\theta)-g(h))^2$ 属于 $[0,D^2]$。由 TV 的有界损失对偶，
$$
|\mathbb E_P\ell_g-\mathbb E_Q\ell_g|\le D^2\delta.
$$
有限情形直接可证：将带符号质量 $P-Q$ 分成正、负部分，两部分质量都为 $\delta$，把 $0\le\ell_g\le D^2$ 分别用于两部分即可。此成熟 TV 期望界也是[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理21.6的共同记录奖励界所用的不等式。对统一解码器类取下确界，分别得到 $R(P)\le R(Q)+D^2\delta$ 及反向，结合共同 $R_C$ 即式（17.16）。$D=0$ 时所有风险和创新均为零；$\delta=0$ 时两律相同，两种情形无需除法。

为证常数锐性，取常值 $C$、$\Theta\sim\operatorname{Bernoulli}(p)$，$0<p<1$，$f(\theta)=\theta$。令 $P$ 中 $H=\Theta$，$Q$ 中 $H\equiv0$，两者定义在相同 $\{0,1\}^2$ 上且来源边缘相同。两律共有 $(0,0)$ 的质量 $1-p$，其余质量 $p$ 分别在 $(1,1)$ 与 $(1,0)$，故 $\delta=p$。前者完全恢复来源，$I(P)=p(1-p)$；后者没有新信息，$I(Q)=0$。于是创新差与 $D^2\delta$ 之比为 $1-p\to1$，任何小于一的统一常数均被足够小的正 $p$ 排除；$p=0,1$ 的退化来源风险均为零。

若 $H$ 是逐步过程的整个末端档案，可在包含不可变来源标签及旧档案的扩充系统上使用机器学习卷定理21.6：要求双方初始 $(\Theta,C)$ 一致、初始摘要按指定映射耦合，并对每个扩充状态和动作统一控制“输出与后继摘要”的联合 TV 缺陷，且摘要保留来源标签。此时该定理给来源—完整记录的 $\delta\le1-(1-\varepsilon)^T$，再代入式（17.16）。只控制未带来源的输出核或末端状态边缘，不满足这个扩充联合输入契约。支撑内条件更新的精确性也不提供稀有分支的统一稳定性；本卷命题12.5已有条件化的 $e/s$ 放大与稀有成功支反例，本定理只控制积分创新。$\square$

**命题 17.10（记录边缘相同不足以控制来源创新）。** 即使 $P_H=Q_H$ 且两律具有相同 $(\Theta,C)$ 边缘，创新也可相差 $1/4$，所以式（17.16）中的来源—记录联合 TV 不能换成记录边缘 TV。

**证明。** 令 $C$ 常值、来源公平、$f(\theta)=\theta$。在 $P$ 下令 $H=\Theta$，在 $Q$ 下令 $H$ 为与来源独立的公平位。两份记录边缘都是公平位，故其 TV 为零。$P$ 下后验为点质量，创新 $1/4$；$Q$ 下后验始终公平，创新零。联合律的 TV 实为 $1/2$，因此没有违反定理17.9。命题17.8已在同一受控模型的两个合法历史中实现同一种联合区别。由此，环境全部未来预测、来源标记未来预测以及完整已获档案是相互关联但不同的任务；它们能否互相恢复，分别取决于定理15.4的可见张成、定理17.7的共同来源核与保留式历史条件，不能由边缘相同或坐标名称代替。$\square$

## 17.99 追加锚

## 18. 局部容量、共同钟率与边界时间取得

**定义 18.1（固定关系图上的容量与物理端口）。** 取有 $n\ge2$ 个顶点的有限连通无向图，每条边具有固定正权；在固定顶点坐标中记其 Laplacian 为 $L$。取正对角容量矩阵 $M$，定义
$$
S_M(t)=\exp(-tM^{-1}L),\qquad t\ge0.
\tag{18.1}
$$
这里直接采用[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节的图关系律：若 $D_G$ 是定向差分、$W$ 是边权对角矩阵，则 $L=D_G^*WD_G$；正顶点权作为容量不要求总和为一。尤其 $L\mathbf1=0$、$\ker L=\mathbb R\mathbf1$，且每个 $L_{ii}>0$。本节比较固定图和固定顶点坐标中的不同常值 $M$，不把顶点重标或状态坐标共轭算作同一个矩阵等式。

固定物理输入 $B:\mathbb R^p\to\mathbb R^n$ 和读出 $H:\mathbb R^n\to\mathbb R^q$。对 $u\in L^1_{\rm loc}([0,\infty);\mathbb R^p)$，状态 $x$ 在每个有限区间绝对连续，动力学几乎处处成立，输出为
$$
M\dot x=-Lx+Bu,\qquad o=Hx.
\tag{18.2}
$$
输入、读出单位和端口身份均保持固定。以下脉冲响应使用零初态，或在固定完整历史下已由制备与独立已知项扣除自由响应的条件；未知初态不因指定 $B,H$ 而自动消失。该取得合同沿用本卷定义13.1、命题13.2及定义13.3的完整记录与共同来源，及[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)命题16.6的初态边界。

**定理 18.2（完整状态演化的常值容量钟刚性）。** 设 $M,N$ 均为正对角矩阵，$\phi:[0,\infty)\to[0,\infty)$ 是任意函数。则
$$
S_N(t)=S_M(\phi(t))\quad\text{对所有 }t\ge0
\tag{18.3}
$$
当且仅当存在 $c>0$ 使
$$
\boxed{\phi(t)=ct\quad(t\ge0),\qquad N=M/c.}
\tag{18.4}
$$
若另有 $\operatorname{tr}N=\operatorname{tr}M$，则 $c=1,N=M$。式（18.3）是全部初态上的完整状态等式；一个边界端口的相同响应不具有此推论。无需预设 $\phi$ 连续或可微。

**证明。** 矩阵指数的标准恒等式 $\det(e^A)=e^{\operatorname{tr}A}$ 给
$$
e^{-t\operatorname{tr}(N^{-1}L)}
=e^{-\phi(t)\operatorname{tr}(M^{-1}L)}.
$$
两个迹均为严格正数，因为它们分别为 $\sum_iL_{ii}/N_{ii}$ 和 $\sum_iL_{ii}/M_{ii}$。实指数单射，故对每个 $t\ge0$，
$$
\phi(t)=ct,\qquad
c=\frac{\operatorname{tr}(N^{-1}L)}{\operatorname{tr}(M^{-1}L)}>0.
$$
行列式这一步只确定共同时间尺度。将已得的线性时间代回完整矩阵等式，在零处取右导数得到
$$
(N^{-1}-cM^{-1})L=0.
$$
因前一因子为对角矩阵，比较第 $i$ 个对角元并用 $L_{ii}>0$，得 $N_{ii}^{-1}=cM_{ii}^{-1}$，即 $N=M/c$。反向代入指数立即得式（18.3）。容量总和相同使 $\operatorname{tr}M/c=\operatorname{tr}M>0$，故 $c=1$。本证明只使用主卷第123.4节的图核与正对角性质及有限维矩阵指数恒等式，不另加能量或熵演化假设。$\square$

**命题 18.3（物理强迫、端口归一化与换钟密度）。** 在定义18.1的制备条件下，固定物理 $B,H$ 给
$$
o_M(t)=\int_0^t K_M(t-s)u(s)\,ds,\qquad
K_M(t)=H S_M(t)M^{-1}B.
\tag{18.5}
$$
因此对 $N=M/c$，
$$
\boxed{K_N(t)=cK_M(ct).}
\tag{18.6}
$$
当 $H=B^*$ 时，令 $C_M=M^{-1/2}LM^{-1/2}$、$J_M=M^{-1/2}B$，则
$$
K_M(t)=J_M^*e^{-tC_M}J_M,\qquad
\lim_{t\to\infty}K_M(t)
=\frac{B^*\mathbf1\mathbf1^*B}{\mathbf1^*M\mathbf1}.
\tag{18.7}
$$
若 $B^*\mathbf1\ne0$，极限非零，未阻尼的 $\int_0^\infty K_M(t)dt$ 不为有限算子积分。特别地，端点端口 $B=e_i$ 保留零模态，不能直接套用恢复几何卷假设15.1及推论16.5的严格正谱积分公式。

对于同一既有响应的时间重标 $t=c\tau$，输入密度必须按本卷定理12.7、恢复几何卷命题15.9运输：
$$
o_M(c\tau)=\int_0^\tau K_M(c(\tau-\sigma))\,
[c\,u(c\sigma)]\,d\sigma.
\tag{18.8}
$$
等价地，在容量 $N=M/c$、输入 $u_N(\sigma)=u(c\sigma)$ 的物理系统中，$o_N(\tau)=o_M(c\tau)$，Jacobian 因子 $c$ 已由 $K_N$ 承担。一般 $C^1$ 严格递增换钟 $\phi$，$\phi(0)=0,\phi'>0$，给同一强迫接口的两时核
$$
o_M(\phi(t))=\int_0^t
\underbrace{\phi'(s)K_M(\phi(t)-\phi(s))}_{\text{相对于 }ds\text{ 的两时核}}
\,u(\phi(s))\,ds.
\tag{18.9}
$$
一个标量曲线 $a k(\phi(t))$ 本身不自动是此强迫接口的脉冲响应密度。

**证明。** 对式（18.2）应用有限维变常数公式得式（18.5）。定理18.2给 $S_N(t)=S_M(ct)$，又有 $N^{-1}=cM^{-1}$，故式（18.6）成立。相似变换
$$
M^{-1}L=M^{-1/2}C_M M^{1/2}
$$
给式（18.7）的对称坐标表达。主卷第123.4节的连通图核结论给 $\ker C_M=\mathbb R M^{1/2}\mathbf1$；谱定理使 $e^{-tC_M}$ 趋向此直线的正交投影，代入得到极限。若 $B^*\mathbf1\ne0$，可取端口向量使该极限的二次型严格正，其时间积分发散，因而算子积分不收敛。式（18.8）与式（18.9）直接应用既有时间运输的积分换元，分别用 $s=c\sigma$ 和旧时间 $s_{\rm old}=\phi(s)$。相应运输状态满足 $d[x_M(\phi(t))]/dt=\phi'(t)[-M^{-1}Lx_M(\phi(t))+M^{-1}Bu(\phi(t))]$，所以输入与生成元同受时间 Jacobian 作用。$\square$

**命题 18.4（三节点端口的完整可见与不可见参数）。** 取单位边权三节点路径
$$
L=\begin{pmatrix}1&-1&0\\-1&2&-1\\0&-1&1\end{pmatrix},\qquad
M_r=\operatorname{diag}(1,r,1),\quad r>0.
\tag{18.10}
$$
固定物理输入、读出为 $B=b,H=b^*$。若 $b=(e_1-e_3)/\sqrt2$，整个响应核为 $e^{-t}$，与 $r$ 无关。若 $b=e_1$，则核为
$$
\boxed{k_r(t)=\frac1{r+2}+\frac12e^{-t}
+\frac{r}{2(r+2)}e^{-(1+2/r)t},}
\tag{18.11}
$$
从而
$$
k_r(0)=1,\qquad k_r'(0)=-1,\qquad
k_r''(0)=1+\frac1r,\qquad k_r(\infty)=\frac1{r+2}.
\tag{18.12}
$$
因此同一图族中，一个固定端口对局部容量完全失明，另一个固定端口的时间关系却含有该容量。可见谱随 $r$ 改变且包含零率，故这个参数族不是恢复几何卷第15节固定严格正谱元组的实例。

**证明。** 广义特征问题 $Lq=\lambda M_rq$ 的三组向量与特征值可取
$$
q_0=(1,1,1)^*,\quad\lambda_0=0;\qquad
q_1=(1,0,-1)^*,\quad\lambda_1=1;\qquad
q_2=(1,-2/r,1)^*,\quad\lambda_2=1+2/r.
$$
它们关于 $\langle v,w\rangle_{M_r}=v^*M_rw$ 两两正交，平方范数依次为 $r+2,2,2(r+2)/r$。命题18.3的对称谱表示等价于
$$
b^*S_{M_r}(t)M_r^{-1}b
=\sum_{j=0}^2e^{-\lambda_jt}
\frac{(b^*q_j)^2}{q_j^*M_rq_j}.
$$
对反对称端口，只有 $j=1$ 的项非零，其权为一；对端点 $e_1$，三个分子均为一，得到式（18.11）。对有限指数和逐项求导给
$$
-k_r'(0)=\frac12+\frac{r}{2(r+2)}\frac{r+2}{r}=1,
\qquad
k_r''(0)=\frac12+\frac{r+2}{2r}=1+\frac1r.
$$
零时值及无穷极限也由式（18.11）直接得到。这里端点的零模态和随 $r$ 改变的正率都是实际物理端口的谱项；比较未知 $r$ 时须使用精确参数纤维，或另证紧凸联合像，或仅使用明确的外界，不能以固定谱的凸合同替换该族。$\square$

**定理 18.5（固定原点的未知增益与常钟率下取得局部容量）。** 在命题18.4的端点制备及物理端口条件下，假设实际取得整条标量响应的零时值、右一阶及右二阶导数。令
$$
F(t)=a k_r(ct),\qquad a,c,r>0,
$$
其中增益 $a$、共同钟率 $c$ 均为未知常数，零标签对应同一经过时间原点。则
$$
\boxed{I=\frac{F(0)F''(0)}{(F'(0))^2}=1+\frac1r>1,\qquad
r=\frac1{I-1}.}
\tag{18.13}
$$
逆映射的局部导数绝对值为 $r^2$。若真实 $I$ 与估计 $\widehat I$ 均不小于 $1+\delta$，$\delta>0$，则
$$
\left|\frac1{\widehat I-1}-\frac1{I-1}\right|
\le\frac{|\widehat I-I|}{\delta^2}.
\tag{18.14}
$$
这是已获得导数关系后的逆误差界，不提供由有限带噪样本估计导数的结论。

**证明。** 式（18.12）及链式法则给 $F(0)=a,F'(0)=-ac,F''(0)=ac^2(1+1/r)$，分母非零，约去 $a^2c^2$ 得式（18.13）。微分 $r(I)=(I-1)^{-1}$ 得 $|r'(I)|=(I-1)^{-2}=r^2$；两个倒数之差的分母为 $(\widehat I-1)(I-1)\ge\delta^2$，给式（18.14）。

这些等式依赖实际零时及导数访问、共同时间原点和固定制备。条件制备、增益恒定及导数误差合同须分别声明；完整曲线的数学存在不赋予这些取得能力。改变 $M_r$ 改变来源动力学，移动读出位置或改变 $B,H$ 改变取得映射。命题18.4的两个固定端口正好区分这两种改变，且不从单端口取得推断一般未知图的识别。$\square$

**命题 18.6（非线性钟的二阶混淆与全曲线极限）。** 保留命题18.4的端点族与未知常增益 $a>0$，设 $\phi:[0,\infty)\to[0,\infty)$ 在零处二次可微，$\phi(0)=0,\phi'(0)>0$。对标量观测 $F(t)=a k_r(\phi(t))$，有
$$
\boxed{\frac{F(0)F''(0)}{(F'(0))^2}
=1+\frac1r-\frac{\phi''(0)}{(\phi'(0))^2}.}
\tag{18.15}
$$
这只给二阶关系中的容量—钟曲率混淆。若另有 $\phi(t)\to\infty$，并具有完整曲线的极限访问，则
$$
\boxed{\frac{F(\infty)}{F(0)}=\frac1{r+2},\qquad
r=\frac{F(0)}{F(\infty)}-2.}
\tag{18.16}
$$
所以式（18.15）不推出任意非线性钟下的全曲线不可识别性。对比值 $J=1/(r+2)$，若 $J,\widehat J\ge\delta>0$，其反演误差同样至多为 $|\widehat J-J|/\delta^2$；该条件不估计无穷极限。

**证明。** 链式法则与式（18.12）给
$$
F'(0)=-a\phi'(0),\qquad
F''(0)=a\left[(1+1/r)(\phi'(0))^2-\phi''(0)\right].
$$
代入并约分得式（18.15）。在只给零处二阶数据时，任取两个正参数 $r,\widetilde r$ 和同一个 $p>0$，把第二条钟的二阶导数改为
$$
\widetilde\phi''(0)=\phi''(0)+p^2(1/\widetilde r-1/r),
\qquad\widetilde\phi'(0)=p=\phi'(0),
$$
即可使两条曲线的零、一、二阶数据相同；这些钟的二阶展开在充分小的右邻域保持正导数。此构造仅匹配二阶数据。若另要求钟趋于无穷，式（18.11）的两个正率项趋零，$F(\infty)=a/(r+2)$，约去 $F(0)=a$ 即得式（18.16）。倒数差给所述误差界。导数访问、极限访问、常增益、制备和误差稳定性是各自独立的假设；式（18.9）还表明该标量重标曲线不应未经输入密度运输就当作非线性换钟的强迫核。$\square$

**命题 18.7（时变容量的两种关系律）。** 取同一固定图 $L$、可微正对角 $M(t)$ 及可微状态 $x(t)$，定义加权总量 $m(t)=\mathbf1^*M(t)x(t)$。若演化律为 $M(t)\dot x(t)=-Lx(t)$，则 $\dot m(t)=\mathbf1^*\dot M(t)x(t)$；若演化律为 $d(M(t)x(t))/dt=-Lx(t)$，则 $\dot m(t)=0$。**证明。** 对第一式使用乘积法则，再用 $\mathbf1^*L=0$；对第二式左乘 $\mathbf1^*$ 即得两项结论。容量为常值时，两种演化律一致；定理18.2比较的是常值容量。$\square$

## 18.99 追加锚

## 19. 共同跳链的路径钟与容量读数距离

**定义 19.1（固定导纳与有限正容量）。** 设 `V` 有限，图连通且至少有两个顶点。令 `w_ij=w_ji≥0`、`w_ii=0`，正权边组成该连通图；记

$$
d_i=\sum_j w_{ij}>0,\qquad
L_{ii}=d_i,\quad L_{ij}=-w_{ij}\quad(i\ne j),
$$
$$
M=\operatorname{diag}(m_i),\qquad
N=\operatorname{diag}(n_i),\qquad m_i,n_i>0.
$$

以行生成元作用于函数的约定，

$$
(Q_Mf)(i)=\frac1{m_i}\sum_jw_{ij}(f(j)-f(i)),
\qquad Q_M=-M^{-1}L.
$$

从 `i` 离开的速率是 `λ_i^M=d_i/m_i`，平均停留时间 `m_i/d_i`；离开后跳到 `j` 的条件概率

$$
P_{ij}=\frac{w_{ij}}{d_i}
\tag{19.101}
$$

与 `M` 无关。

这里 `e^{tQ_M}f(i)=E_i[f(X^M_t)]` 是向后半群，解 `M ḟ=−Lf`。若 `p` 是列概率质量，则它解向前方程

$$
\dot p=Q_M^Tp=-LM^{-1}p,
\qquad \sum_i p_i=1.
$$

不能把质量 `p` 和相对参考密度/状态函数混作同一坐标。

这一生成元沿用[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节。路径换钟的成熟背景为 Andres–Deuschel–Slowik, *Heat kernel estimates and intrinsic metric for random walks with general speed measure under degenerate conductances*, arXiv:1711.11119v2，式(1.1)及其后关于速度测度的说明；以下只使用有限图。

**定理 19.2（同一跳链、指数等待与路径换钟）。** 定义19.1的两份容量可以耦合在同一随机来源上，使 $X^N(t)=X^M(A^{-1}(t))$，其中 $A(s)=\int_0^s n_{X^M_u}/m_{X^M_u}\,du$。

证明。在同一个概率空间上取：

- 初态 `Z₀` 服从任意指定的共同分布 `ν`；
- 从该初态开始、转移矩阵为式（19.101）的离散 Markov 跳链 `Z₀,Z₁,…`；
- 与整条跳链独立的 iid 随机数 `E₀,E₁,…∼Exp(1)`。

对两份容量使用**同一** `Z_k,E_k`，定义

$$
H_k^M=\frac{m_{Z_k}}{d_{Z_k}}E_k,
\qquad
H_k^N=\frac{n_{Z_k}}{d_{Z_k}}E_k,
$$
$$
T_0^M=T_0^N=0,\qquad
T_k^M=\sum_{j<k}H_j^M,\quad
T_k^N=\sum_{j<k}H_j^N.
$$

在 `[T_k^M,T_(k+1)^M)` 上置 `X^M_s=Z_k`，`N` 链同理。给定当前访问状态 `i`，`H_k^M` 是速率 `d_i/m_i` 的指数等待，与该次下一跳选择独立，故这正是生成元 `Q_M` 的链。`N` 链同理具有生成元 `Q_N`。

有限性和严格正容量给

$$
0<\min_i\frac{m_i}{d_i}\le\max_i\frac{m_i}{d_i}<\infty,
$$

`N` 也一样。iid 正指数变量之和几乎处处发散，所以两组跳跃时刻都趋于无穷；等价地，有限最大退出速率给标准非爆炸保证。每个有限时间窗只有有限次跳跃，右连续路径在所有非负时间上定义。

这项构造是数学耦合，建立在同一完整随机来源上。它不证明两次实际实验天然共享相同随机数；若要将耦合解释为可执行实验转换，还须提供合法制备、干预与数据取得合同。

继续核对时钟的方向。

令 `α_i=n_i/m_i`，有限正容量给常数

$$
0<\alpha_{\min}\le\alpha_i\le\alpha_{\max}<\infty.
$$

于是逐路径

$$
A(s)=\int_0^s\alpha_{X^M_u}\,du
$$

连续、严格递增，满足 `α_min s≤A(s)≤α_max s`，且趋于无穷。因此它有唯一连续严格递增逆函数 `T(t)=A⁻¹(t)`，对所有 `t≥0` 定义。

在第 `k` 段停留区间，`A` 的斜率是 `n_(Z_k)/m_(Z_k)`，所以

$$
A(T_{k+1}^M)-A(T_k^M)
=\frac{n_{Z_k}}{m_{Z_k}}H_k^M
=H_k^N.
$$

从零点累加即得

$$
\boxed{A(T_k^M)=T_k^N,\qquad
X^M(A^{-1}(t))=X^N(t).}
\tag{19.102}
$$

等式包括跳跃时刻，采用上述右连续区间约定。记 $Y_t=X^M(A^{-1}(t))$，由该恒等式，$Y$ 恰有生成元 $Q_N$。形式上逆钟的几乎处处导数为

$$
T'(t)=\frac{m_{Y_t}}{n_{Y_t}},
$$

对应生成元的逐行缩放 `Q_N=diag(m_i/n_i)Q_M`。若容量增加为 `N=αM`，则 `A(s)=αs`、`Y_t=X^M_(t/α)`，与生成元 `Q_N=Q_M/α` 一致。

一般 `A` 依赖实际访问状态，且与轨迹相关。它是适应于该路径的连续加性泛函；逆钟可作原过滤族的停止时刻，时间改变后的过程使用相应改变的过滤族。此处的 Markov 性与生成元已经由共同指数等待构造直接认证，不必假设任意随机换钟都会保持 Markov 性。

逆向重建也使用同一路径：

$$
A^{-1}(t)=\int_0^t\frac{m_{Y_v}}{n_{Y_v}}\,dv.
$$

不能将 `A` 单独抽样后与另一条独立的 `X^M` 组合：那一般不再给式（19.102）的联合律。

有限图的全时间结论不能仅凭“每个顶点容量为正”搬到无限图。无限图还须另证原链非爆炸及 `A(s)→∞`；没有全局正下界的比率可能把无限原时间压缩到有限新时间。本节的有限性已排除这些问题。

**命题 19.3（跳跃顺序、时间占据与初始律）。** 耦合逐路径保留完整的访问状态序列，包括事件顺序、按跳数计的到达位置及不依赖等待时间的首次命中事件。实际第 `k` 次跳跃时刻由 `T_k^M` 变成 `T_k^N`；固定物理时刻前的跳数、定时状态分布、停留时长和时间折扣量一般改变。

证明。对不同顶点 $i,j$，两条链分别满足详细平衡：

$$
\pi_i^M=\frac{m_i}{\sum_jm_j},\qquad
\pi_i^MQ_M(i,j)=\frac{w_{ij}}{\sum_km_k}
=\pi_j^MQ_M(j,i),
$$

`N` 的唯一平稳分布则是 `π_i^N=n_i/Σn`。总概率守恒并未丢失；变化的是同一条访问序列在时间轴上的驻留比例。

跳链自己的不变分布是

$$
\widehat\pi_i=\frac{d_i}{\sum_jd_j},
$$

与容量无关。它描述按访问次数计的平稳权重；不等于连续时间链的时间占据分布。有限图跳链可以有周期，不能因此附带声称其每步边缘律总是收敛。

对角项的平衡等式恒真，连通性使链不可约，有限不可约链的平稳分布唯一。沿各停留段对 $t=A(s)$ 换元，时间占据的转换有精确 Jacobian：对任意状态函数 `g` 和原时间终点 `S`，

$$
\boxed{
\int_0^{A(S)}g(Y_t)\,dt
=\int_0^Sg(X^M_s)\frac{n_{X^M_s}}{m_{X^M_s}}\,ds.
}
\tag{19.103}
$$

结合有限不可约连续时间链的遍历定理（Norris, *Markov Chains*, Cambridge University Press, 1997，第3章），归一化时间占据由 `π^M_i` 乘 `n_i/m_i` 后再归一化，正好得到 `π^N_i`。

初始分布必须另行保留：式（19.102）的耦合有 `Y₀=X₀^M`。若原链从 `π^M` 启动，新链也从 `π^M` 启动，通常**不是**从 `π^N` 启动。不能仅凭路径换钟声称两边从各自稳态启动且仍共享同一初态。要构造新链的平稳版本，须使用正确初始律或相应的时间原点加权；这与现有同初态耦合是不同的准备合同。

**命题 19.4（随机路径钟与完整半群钟的不同量词）。** 确定共同钟要求一个不依赖初态、随机实现或观测端口的函数 `φ`，使

$$
e^{tQ_N}=e^{\phi(t)Q_M}\quad\text{对全部 }t\ge0
$$

作为算子恒等。固定非平凡连通图时，由本卷定理18.2，该条件只容许 `N=M/c`、`φ(t)=ct`。比例情形恰是式（19.102）中状态无关的特例。

非比例时，定理19.2给出的却是

$$
e^{tQ_N}f(i)=E_i^M\big[f(X^M_{A^{-1}(t)})\big],
$$

其中随机时间 `A⁻¹(t)` 与该路径共同生成。一般不能将它改成 `e^{E[A⁻¹(t)]Q_M}`，也不能仅按随机时间的边缘分布对 `e^{sQ_M}` 作独立混合：给定停止时间的事件会同时改变路径的条件律。

因此“状态路径可由依赖路径的钟对应”不推出“平均热场在同一时刻相同”，更不推出固定输入、固定读出、固定采样表的响应核相同。它允许相同跳跃关系与不同相对衰减谱同时存在，也允许先前的三点路径例子中确定性状态场轨迹方向随容量改变。

**命题 19.5（粗读数上的钟可识别条件与反例）。** 若完整记录给出了全部真实跳跃状态、跳跃时刻以及同源已知的 `m,n`，则可以逐段重建 `A`，并给旧事件附上新标签 `A(T_k^M)`。旧时间、原始记录和来源身份必须保留，不能用新标签覆盖掉原来已经取得的实验事实。重标同一事件也不等于在新钟的等距时刻重新采样。

对粗读出 `h:V→O`，一个直接充分条件是比率在每个读出纤维上恒定：

$$
\alpha_i=\bar\alpha(h(i)).
$$

若完整连续读出及其原时间戳可取得，则

$$
A(s)=\int_0^s\bar\alpha(h(X^M_u))\,du
$$

可以从该读出计算。仅有有限离散时刻的读数仍不自动给出所有区间内驻留时间，需另有取得或估计证书。

相反，若存在仍被完整档案允许的 `i,j`，满足 `h(i)=h(j)` 但 `n_i/m_i≠n_j/m_j`，并允许它们作为备选初态，那么在一个固定正时间窗内“不跳跃”的事件在两种初态下分别具有概率 $e^{-d_iS/m_i}>0$、$e^{-d_jS/m_j}>0$，其中 $S>0$ 是窗口长度。两份完整粗读出都是同一个常值时间记录，却有

$$
A_i(s)=(n_i/m_i)s\ne(n_j/m_j)s=A_j(s).
$$

于是该粗读出本身不确定路径钟。这个例子针对所列允许状态与记录纤维；若旧档案已经识别了初态、提供了内部轨迹或排除了其中一份实现，必须把这些信息一起使用，不能删除它们来制造不可识别性。

局部响应核还可能连某些动力学模式都看不见。例如三点路径 `M_r=diag(1,r,1)` 的固定端口 `u=(1,0,−1)/√2` 对所有 `r` 都给核 `e^(−t)`，但这既不提供实现路径钟所需的状态驻留信息，也不使完整状态半群相同。可见平均响应、一次实际路径及其时钟是不同的观测对象，必须保持各自的共同来源关系。

移动观察者、改变端口或主动制备若改变导纳、容量、干预规则或读取权限，已经改变定义19.1的固定模型/取得合同。数学上存在这个换钟，不赋予观察者访问隐藏状态、修改真实等待时间或执行相同随机来源的能力。

**命题 19.6（能量恒等与容量规范）。** 固定有限连通图 `V`，至少两个顶点。边上 `w_xy=w_yx>0`，无边为零，`w_xx=0`；顶点容量 `m_x>0`。记

$$
d_x=\sum_yw_{xy},\quad L=D^{\mathsf T}WD,
\quad (Q_mf)(x)=\frac1{m_x}\sum_yw_{xy}(f(y)-f(x))=(-M^{-1}Lf)(x).
$$

把 $\langle f,g\rangle_m=\sum_xm_xf(x)g(x)$ 固定为参考内积；对称导纳使每条无向边的两项相加为平方差乘积，因此同一能量形式为

$$
\mathcal E_w(f,g)=\sum_{\{x,y\}\in E}w_{xy}(f(y)-f(x))(g(y)-g(x))
=\langle f,-Q_mg\rangle_m.
\tag{19.111}
$$

固定 `w` 时，能量形式的这一表达不随 `m` 改变；改变的是参考内积、生成元和下面读数的局部预算。顶点 `x` 的退出速率是 `d_x/m_x`，平均停留时间是 `m_x/d_x`，跳到 `y` 的条件概率 `w_xy/d_x` 不变。

整体缩放 `n=αm` 给出精确关系

$$
Q_{\alpha m}=Q_m/\alpha,\qquad
e^{tQ_{\alpha m}}=e^{(t/\alpha)Q_m},\qquad
H_k^{\alpha m}=\alpha H_k^m
\tag{19.112}
$$

（最后一式使用同一跳链、同一指数等待随机数）。若一般容量满足

$$
0<a\le n_x/m_x\le b<\infty\quad\text{对所有 }x,
\tag{19.113}
$$

则定理19.2的共同路径换钟

$$
A(s)=\int_0^s\frac{n_{X^m(u)}}{m_{X^m(u)}}\,du
$$

满足 `as≤A(s)≤bs`、`t/b≤A⁻¹(t)≤t/a`，每次共同访问的等待时间也满足 `aH_k^m≤H_k^n≤bH_k^m`。非比例时，这不是一个所有初态和路径通用的确定时钟，不给半群逐项大小排序。

[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节 使用归一化概率参考 `μ`。本题保留任意正容量的绝对尺度；若令 `μ=m/Σm`，要保留 `Q_m` 就须同时把边导纳改成 `w/Σm`。只归一化容量会改变时钟，不能省略总容量因子。

**定义 19.7（截断逐边长度的路径距离）。**

令

$$
r_m(e)=\frac{\min(m_x,m_y)}{w_{xy}},\qquad
\ell_m(e)=\sqrt{\min\{1,r_m(e)\}}
\quad(e=\{x,y\}),
$$
$$
\boxed{\ d_m^{\rm ADS}(i,j)=\inf_{\gamma:i\leadsto j}\sum_{e\in\gamma}\ell_m(e).\ }
\tag{19.114}
$$

这正是论文取 `θ=m, ω=w` 的式 (1.2)。`1` 与**整个比值**取最小值，不是把容量先与 1 取最小值再除以导纳。有限连通图与正边长使它成为有限距离，且 `d_m^{ADS}≤d_graph`。

**命题 19.8（逐边对偶、缩放与截断）。** Andres–Deuschel–Slowik 的 Proposition 2.3 给精确对偶形式

$$
d_m^{\rm ADS}(i,j)=\sup\left\{f(j)-f(i):
|f(y)-f(x)|\le1,\quad
w_{xy}|f(y)-f(x)|^2\le\min(m_x,m_y)\quad\forall\{x,y\}\in E\right\}.
\tag{19.115}
$$

这是**逐边**约束。论文的 `dΓ^ω(f,f)(e)=w_e(Df(e))²` 是这里的边能量读数；它不是下一节把所有邻边在一个顶点相加的预算。使用论文的 intrinsic 名称时必须保留这份定义。比如三叶单位星、全部容量为 1 时，式（19.114） 是图距离，中心的 `Σ_y w_xy d(x,y)²=3>2m_x`，所以仅引用论文名词也不能推出本题的顶点平方和条件。

证明。整体容量缩放时的准确式子是

$$
\ell_{\alpha m}(e)=\sqrt{\min\{1,\alpha r_m(e)\}}.
\tag{19.116}
$$

因此

$$
\min\{1,\sqrt\alpha\}\,d_m^{\rm ADS}
\le d_{\alpha m}^{\rm ADS}
\le\max\{1,\sqrt\alpha\}\,d_m^{\rm ADS}.
\tag{19.117}
$$

若所有边在缩放前后都未超过截断，即 `max{1,α}r_m(e)≤1`，则所有边长共同乘以 `√α`，这时才有全距离的 `d_{αm}^{ADS}=√α d_m^{ADS}`。这是一个明确充分条件，不是逐点相等的必要条件。反例只需一条权为 1、两端容量为 1 的边：容量乘以 4 后，等待时间乘以 4，但距离仍为 1，不是 2。有限图上，当 `α≥max_e w_e/min(m_x,m_y)` 时，所有边长均为 1，距离恰为图距离，继续增加容量不再改变这份截断距离。

一般比率合同 （19.113） 给

$$
\boxed{\ \min\{1,\sqrt a\}\,d_m^{\rm ADS}
\le d_n^{\rm ADS}
\le\max\{1,\sqrt b\}\,d_m^{\rm ADS}.\ }
\tag{19.118}
$$

依据是逐边 `a r_m(e)≤r_n(e)≤b r_m(e)`，对 `min(1,·)` 保留截断后再对路径求和、取下确界。不能省去式（19.118） 两侧的 `min/max`。

**定义 19.9（同一顶点预算的能量读数距离）。**

现在独立定义

$$
\mathcal F_m=\left\{f:V\to\mathbb R:
\sum_yw_{xy}(f(y)-f(x))^2\le2m_x\quad\forall x\right\},
$$
$$
\boxed{\ D_m(i,j)=\sup_{f\in\mathcal F_m}|f(i)-f(j)|.\ }
\tag{19.119}
$$

**定理 19.10（能量读数距离与容量比较）。** 等价地，`Γ_m(f)(x)=(2m_x)⁻¹Σ_yw_xy(f(y)−f(x))²≤1`；因子 2 在这里固定，不与论文的逐边约定混用。所有点对使用同一个 `𝓕_m`，因此直接承接本卷定理2.2的固定读数族上确界伪度量结构。可行函数在每条边的差不超过 `√[2min(m_x,m_y)/w_xy]`，连通性给有限的路径上界。取 $\delta=\min_x\sqrt{2m_x/d_x}>0$，函数 $\delta\mathbf1_{\{i\}}$ 在每个顶点的平方差和不超过 $\delta^2d_x\le2m_x$，且分离 $i$ 与任意其他顶点。因此在当前有限连通模型上它确为距离。

它没有逐边 `1` 截断，齐次性准确给出

$$
\mathcal F_{\alpha m}=\sqrt\alpha\,\mathcal F_m,
\qquad
\boxed{\ D_{\alpha m}=\sqrt\alpha\,D_m.\ }
\tag{19.120}
$$

对 （19.113），同一个可行集包含关系

$$
\sqrt a\,\mathcal F_m\subseteq\mathcal F_n
\subseteq\sqrt b\,\mathcal F_m
$$

给出

$$
\boxed{\ \sqrt a\,D_m(i,j)\le D_n(i,j)\le\sqrt b\,D_m(i,j).\ }
\tag{19.121}
$$

这些是对同一组 `w`、同一顶点及整体可行读数族的比较；无需把不同点对的最优读数认作同一函数。

**命题 19.11（逐对上确界不保留同一顶点预算）。**

取路径 `0—1—2`，两条导纳和三个容量都为 1。可行性恰要求

$$
(f_0-f_1)^2\le2,\quad
(f_0-f_1)^2+(f_2-f_1)^2\le2,\quad
(f_2-f_1)^2\le2.
$$

| 标识 | 点对 | 精确距离 | 达到上界的读数 `(f₀,f₁,f₂)` | 三个顶点的平方和 |
| --- | --- | --- | --- | --- |
| 19.11表1行1 | `(0,1)` | `√2` | `(√2,0,0)` | `(2,2,0)` |
| 19.11表1行2 | `(1,2)` | `√2` | `(0,0,√2)` | `(0,2,2)` |
| 19.11表1行3 | `(0,2)` | `2` | `(1,0,−1)` | `(1,2,1)` |

前两项上界来自单边约束，第三项上界来自 `(f₀−f₂)²≤2[(f₀−f₁)²+(f₂−f₁)²]≤4`，所以表中等式全部是精确结果。中心顶点却有

$$
\boxed{\ \sum_yw_{1y}D_m(1,y)^2=2+2=4>2=2m_1.\ }
\tag{19.122}
$$

甚至距离函数 `g(y)=D_m(1,y)` 本身也不属于 `𝓕_m`。逐对最优函数分别花满中心预算，但不能同时占用这两份预算；将每个坐标的上确界拼成向量正是失效步骤。它不影响三角不等式，因为对每个固定可行函数，三角界由同一函数给出，再对单个左端取上确界即可。

同一三点模型中，论文距离的相邻值均为 1、端点值为 2；能量读数距离的相邻值均为 `√2`、端点值为 2。因此两者甚至不是在这个实例上相差一个共同常数。

**推论 19.12（同一容量尺度的时间与距离平方）。** 在固定导纳下，$m\mapsto\alpha m$ 使定理19.2的每次等待乘 $\alpha$、定理19.10的 $D_m^2$ 乘 $\alpha$；定义19.7的截断距离仅在命题19.8的未截断条件下具有同一齐次关系。证明。分别代入所引三项的缩放公式即得。一般 $am\le n\le bm$ 时，路径钟满足 $as\le A(s)\le bs$，能量距离满足 $\sqrt aD_m\le D_n\le\sqrt bD_m$，截断距离保留命题19.8的最小值、最大值因子。这些是指定生成元与两种指定距离的数学关系，不是命中时间等式或物理速度定律；可行读数的上确界也不表示这些读数已被共同取得。$\square$

## 20. 非线性共同钟的有限纤维与完整历史

**假设 20.1（有限端点记录与自由光滑钟）。** 使用命题18.4的 $k_r$，$r>0$，同源响应为 $F(s)=a k_r(\phi(s))$，$a>0$。真实零点、稳定增益、制备和全部旧档案按[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)假设19.1保留。当前有限记录是
$$
0=s_0<s_1<\cdots<s_n<\infty,\qquad
1=z_0>z_1>\cdots>z_n>0,\qquad F(s_i)=az_i.
$$
钟类暂取 $\phi\in C^\infty([0,\infty))$，$\phi(0)=0$，$\phi'>0$，$\phi(s)\to\infty$。$n=0$ 时相邻不等式为空。以下精确纤维针对所列记录；若旧档案另有钟或来源限制，须与其共同相交，不能用本节纤维覆盖旧信息。

**定理 20.2（任意有限前缀的精确参数投影）。** 在假设20.1且无其他限制时，相容参数恰为
$$
\mathcal R_D=\{r>0:p_r<z_n\}
=\bigl(\max\{0,z_n^{-1}-2\},\infty\bigr),\qquad p_r=\frac1{r+2}.
\tag{20.101}
$$
相容性的量词是对每个候选 $r$ 存在一条可依赖 $r$ 的共同钟，拟合该份全部有限记录。

证明。由命题18.4，$k_r(0)=1$，$k_r'(t)=-(e^{-t}+e^{-(1+2/r)t})/2<0$，$k_r(t)\to p_r$，且每个有限 $t$ 有 $k_r(t)>p_r$。因此 $k_r:[0,\infty)\to(p_r,1]$ 连续严格递减双射。有限标签只能给有限内部时间，故 $z_n>p_r$ 必要，等号不能拟合。

反之，设 $n\ge1$ 且 $p_r<z_n$。令 $t_i=k_r^{-1}(z_i)$，则 $0=t_0<t_1<\cdots<t_n<\infty$。写 $\Delta s_i=s_i-s_{i-1}$、$\Delta t_i=t_i-t_{i-1}$，选择
$$
0<\varepsilon<\min_{1\le i\le n}\frac{\Delta t_i}{\Delta s_i}.
$$
在每个开区间 $(s_{i-1},s_i)$ 取非负、积分为一的 $C_c^\infty$ 隆起函数 $b_i$，向区间外延拓为零，置
$$
d(s)=\varepsilon+\sum_{i=1}^n(\Delta t_i-\varepsilon\Delta s_i)b_i(s),
\qquad \phi(s)=\int_0^s d(u)\,du.
\tag{20.102}
$$
每个系数正，故 $d\ge\varepsilon>0$；紧支撑严格位于区间内部，零延拓及其有限和在全部标签和原点光滑。每段积分为 $\varepsilon\Delta s_i+\Delta t_i-\varepsilon\Delta s_i=\Delta t_i$，所以 $\phi(s_i)=t_i$。末点以后 $\phi(s)=t_n+\varepsilon(s-s_n)$，故无界。若 $n=0$，直接取 $\phi(s)=s$，不对空集取最小值。全部正参数均满足 $p_r<z_0=1$。这证明充分性。

若 $z_n<1/2$，记录给严格下界 $r>z_n^{-1}-2$；若 $z_n\ge1/2$，每个正参数都相容。早期数值和时间间隔约束插值钟，但在此钟类中不给额外的 $r$ 限制。这沿用恢复几何卷引理15.8的单调反演机制；该引理严格正生成元的零平台值域在这里换成精确的 $(p_r,1]$，不搬用其原值域。$\square$

**命题 20.3（完整无界历史与有限前缀的量词差）。** 若 $s_j\to\infty$ 且一对 $(r,\phi)$ 同时实现所有记录，则
$$
\ell=\lim_j z_j=p_r,\qquad r=\ell^{-1}-2,\qquad 0<\ell<1/2.
$$
但每个有限前缀分别有一条无界钟，并不保证全部历史有一条共同钟。

证明。共同钟无界且递增，故 $\phi(s_j)\to\infty$，代入 $k_r$ 的平台极限得到首项。若实际参数为 $r_0$，$z_j\downarrow p_{r_0}$，任意固定 $r>r_0$ 都因 $p_r<p_{r_0}<z_j$ 而通过每个有限前缀。然而此候选所需时间满足
$$
k_r^{-1}(z_j)\longrightarrow k_r^{-1}(p_{r_0})<\infty,
$$
所以不存在在全部 $s_j\to\infty$ 取这些值的无界共同钟。即 $\forall n\,\exists\phi_n$ 不推出 $\exists\phi\,\forall j$。只有无穷多个标签而标签有界时，不能使用这里的平台论证；平台极限也不是有限预算自动取得的样本。$\square$

**定义 20.4（已知共同钟率界）。** 给 $0<m\le M<\infty$，用 $\mathcal C_{m,M}$ 表示全部 $\phi(0)=0$ 且满足
$$
m(v-u)\le\phi(v)-\phi(u)\le M(v-u)\qquad(0\le u\le v)
\tag{20.103}
$$
的连续钟。这等价于局部绝对连续且几乎处处 $m\le\phi'\le M$：一个方向积分导数，另一个方向由 Lipschitz 函数的绝对连续性、几乎处处可微性及差商界得到。特别 $\phi(s)\ge ms$，无界性自动成立。定义 $t_i(r)=k_r^{-1}(z_i)$、$t_0=0$、$\Delta_i(r)=t_i(r)-t_{i-1}(r)$ 和 $L_i=s_i-s_{i-1}>0$，逆仅在 $p_r<z_n$ 时使用。

**定理 20.5（绝对连续钟的精确增量判据）。** 若 $n\ge1$，相容参数集恰为
$$
\mathcal R_{\rm AC}={r>0:p_r<z_n,\quad
mL_i\le\Delta_i(r)\le ML_i\ (1\le i\le n)\}.
\tag{20.104}
$$
$n=0$ 时每个正参数相容。$m=M$ 时唯一钟为 $\phi(s)=ms$，条件化为 $t_i(r)=ms_i$。

证明。对相邻标签应用式（20.103）给必要性。反向，在每段线性插值 $\phi(s_i)=t_i(r)$，斜率 $\Delta_i/L_i\in[m,M]$；末点以后以任意固定 $[m,M]$ 内斜率延伸，即得全域绝对连续钟。两端速率等号允许，但有限时间平台等号不允许。$n=0$ 取任一合法线性钟，$m=M$ 则式（20.103）本身强制唯一钟。

只检查从原点累计的 $ms_i\le t_i\le Ms_i$ 不够。例如 $m=1,M=2,s_1=1,s_2=2,t_1=2,t_2=21/10$ 满足累计界，却有 $t_2-t_1=1/10<1$。任取正 $r$ 并令 $z_i=k_r(t_i)$，就在本模型中实现这些读数及该失败。$\square$

**定理 20.6（光滑钟的饱和邻接判据）。** 设 $m<M$。对固定满足式（20.104）的 $r$，令 $c_i=\Delta_i/L_i$，把 $c_i=m$、$c_i=M$ 分别称为下界、上界饱和。存在全域 $C^\infty$ 钟且处处 $m\le\phi'\le M$，当且仅当不存在两个相邻区间分别饱和于相反端点。

证明。若连续导数 $d\in[m,M]$ 在一段均值为 $m$，则非负连续函数 $d-m$ 积分为零，故该闭段处处 $d=m$；均值为 $M$ 同理。相反饱和邻段在共同端点要求两个不同导数，矛盾。

反向，在每个标签选导数值 $q_j\in[m,M]$。饱和邻段规定它等于其端点界，两侧规定相容恰是所述条件；没有规定时可取 $(m+M)/2$。饱和区间上取常导数。在内点斜率区间，把其长度、目标均值及端点导数写为 $L,c,A,B$，其中 $m<c<M$。取端点附近支撑互不相交的光滑截断 $\rho_0,\rho_1\in[0,1]$，各自近相应端点恒为一，远离端点为零，令
$$
\alpha=\int_0^L\rho_0,\quad\beta=\int_0^L\rho_1,\quad
v=\frac{cL-A\alpha-B\beta}{L-\alpha-\beta}.
$$
缩小支撑使 $\alpha+\beta<L$ 且 $v\in(m,M)$，这是因为 $v\to c$。置
$$
d(u)=v+(A-v)\rho_0(u)+(B-v)\rho_1(u).
\tag{20.105}
$$
支撑不相交使每点是 $v$ 与至多一个端点值的凸组合，故 $m\le d\le M$。积分恰为 $cL$，两端邻域为指定常数，因而各段光滑拼接。末点以后取最后端点的常导数，积分即得所需钟。故严格内点斜率充分但非必要；孤立饱和段及同端饱和邻段均可接受。$m=M$ 已由定理20.5处理。$\square$

**命题 20.7（逆时间增量的参数单调性与闭性）。** 对固定有限记录，每个 $\Delta_i(r)$ 在 $D=\{r>0:p_r<z_n\}$ 连续严格递减。因此 $\mathcal R_{\rm AC}$ 是相对于 $(0,\infty)$ 闭的区间，可为空或单点；其与正参数紧集的交为紧集。光滑可行参数集要么为空，要么恰等于 $\mathcal R_{\rm AC}$。

证明。令 $\lambda_r=1+2/r$，使用恢复几何卷定理19.2的参数导数和命题18.4的时间导数，隐函数求导得
$$
\partial_r k_r^{-1}(z)=-H_r(k_r^{-1}(z)),\qquad
H_r(t)=\frac{2[1-(1+\lambda_rt)e^{-\lambda_rt}]}
{(r+2)^2(e^{-t}+e^{-\lambda_rt})}.
\tag{20.106}
$$
$H_r(0)=0$；分子在 $t>0$ 正且严格递增，其导数除正常数外为 $\lambda_r^2te^{-\lambda_rt}$，正分母严格递减，故 $H_r$ 严格递增。于是
$$
\Delta_i'(r)=-H_r(t_i(r))+H_r(t_{i-1}(r))<0.
$$
连续性由时间导数非零的隐函数定理给出。每项上下界的逆像都是区间；上速率界限制参数下端，下速率界限制参数上端，交仍是区间。

闭性还需检查严格平台边界。若可行 $r_j\to r_*>0$，则 $t_n(r_j)\le Ms_n$，所以 $k_{r_j}(Ms_n)\le z_n$。取极限得 $p_{r_*}<k_{r_*}(Ms_n)\le z_n$。逆时间在该点有定义且连续，所有增量不等式传到极限，故相对闭。

若某个 AC 可行 $r_*$ 有定理20.6的相反饱和邻段，则其中一个增量等于下界，另一个等于上界。严格递减性使每个 $r>r_*$ 违反前者下界、每个 $r<r_*$ 且在 $D$ 内者违反后者上界；$D$ 外已不可行。因此整个 AC 集只有 $r_*$，而光滑集为空。若没有这种候选，全部 AC 可行参数均能光滑实现，证明最后结论。它没有省略饱和条件，也没有断言光滑钟族在局部一致拓扑中闭。$\square$

**定理 20.8（紧参数与共同钟的完整记录实现）。** 固定非空紧集 $K\subset(0,\infty)$。若每个有限记录子集在同一 $K\times\mathcal C_{m,M}$ 中有共同实现，则全部记录有一对共同实现 $(r_*,\phi_*)$。附加约束在此联合拓扑下闭时可以一并保留。

证明。钟取紧区间上一致收敛拓扑。每个钟 $M$-Lipschitz，$[0,T]$ 上取值在 $[0,MT]$，原点与式（20.103）在局部一致极限下闭。直接应用紧开形式的 Arzelà–Ascoli 定理，$\mathcal C_{m,M}$ 紧。其使用条件分别是局部等度连续、逐点紧值界和闭性；无需另证一份一般紧性定理。$K\times\mathcal C_{m,M}$ 亦紧，且每条条件 $k_r(\phi(s_i))=z_i$ 由评价与 $(r,t)\mapsto k_r(t)$ 连续而为闭集。紧集的闭集有限交性质给全部条件的共同点。顺序历史亦可用嵌套非空紧集交定理。极限仍有 $\phi_*(s)\ge ms$，所以无界。

这里复用 Mathlib 的 `ArzelaAscoli.compactSpace_of_isClosedEmbedding` 和 `IsCompact.inter_iInter_nonempty` 所表述的一般紧性结论。每次改变 $K$、丢弃旧记录、只检查各条记录单独可行均不满足共同有限交前提。导数读数不自动对局部一致拓扑连续，需另加相应拓扑合同。上界 $M$ 提供局部有界和等度连续；下界 $m>0$ 使无界性保留；只有各钟分别无界不是闭条件。$\square$

**定理 20.9（局部有限的无界标签上的共同光滑钟）。** 设 $s_j\uparrow\infty$，每个有限前缀在同一紧集 $K\subset(0,\infty)$ 中有光滑可行参数，钟率共同在 $[m,M]$。则有单一 $r_*\in K$ 与单一全域光滑钟实现全部历史。

证明。固定候选 $r$ 时，若每个前缀满足式（20.104），在全部相邻区间分段线性插值已得共同 AC 钟，且 $t_j(r)\ge ms_j\to\infty$。对参数变化的光滑情形，由命题20.7，每个非空前缀光滑参数集等于对应 AC 集，与 $K$ 的交紧且嵌套。嵌套紧交定理给 $r_*$，它满足所有有限前缀的增量和饱和邻接条件。在每个相邻区间按定理20.6构造导数，标签导数依两侧饱和段统一选择。$s_j\to\infty$ 使任一有界区间只有有限接点，近接点的常导数片段保证全域光滑。积分后给共同钟。$m=M$ 时直接取线性钟。

此证明使用参数闭性和显式重建，不把光滑钟的局部一致极限宣称为光滑。命题20.3中固定 $r>r_0$ 的反例在这里必失败于某个有限前缀，因为其必需逆时间有界而 $ms_j\to\infty$。对任何实际共同实现，平台仍唯一确定 $r_*$，并不确定孤立标签之间的钟。$\square$

**命题 20.10（没有紧参数控制时的逃逸）。** 取 $m=1,M=2,s_j=j,z_j=e^{-j}$。每个有限前缀有正有限参数的光滑实现，全部历史却没有任何有限正参数实现。

证明。$r\to\infty$ 时 $k_r(t)\to e^{-t}$；对每个固定 $i$，逆 $t_i(r)\to i$，因而 $\Delta_i(r)\to1$。逆收敛可由严格单调性在 $i\pm\eta$ 两侧夹逼得到。若 $g_r(s)=k_r^{-1}(e^{-s})$ 有定义，$s>0$ 时
$$
g_r'(s)=\frac{k_r(g_r(s))}{-k_r'(g_r(s))}>1,
\qquad k_r(t)+k_r'(t)=p_r(1-e^{-(1+2/r)t})>0.
$$
每个固定前缀的大参数因而同时具有 $1<\Delta_i(r)<2$，由定理20.6光滑可行。但完整 $z_j\to0$，与任何正有限 $r$ 的正平台矛盾。共同钟率界不替代参数紧性。$\square$

**命题 20.11（有限聚点使逐前缀光滑性不能拼接）。** 设 $m<M$，固定 $r_0>0$，令
$$
u=\frac{2m+M}{3},\quad v=\frac{m+2M}{3},\quad
s_i=1-2^{-i}\ (i\ge0),\quad c_i=u,v,u,v,\ldots,
$$
$$
t_0=0,\qquad t_i=\sum_{j=1}^i c_j2^{-j},\qquad z_i=k_{r_0}(t_i).
$$
每个有限前缀在同一紧集 $K=\{r_0\}$ 中光滑可行，整份历史有 AC 实现，却没有 $C^1$ 实现。

证明。全部区间斜率严格在 $(m,M)$，故有限光滑可行由定理20.6给出。逐段线性插值，在 $s=1$ 取连续极限，之后以 $[m,M]$ 内常率延伸，给共同 AC 钟。若有 $C^1$ 钟，严格反演强制 $\phi(s_i)=t_i$，均值定理在每段给 $\xi_i\in(s_{i-1},s_i)$，使 $\phi'(\xi_i)=c_i$。$\xi_i\to1$ 与导数连续性强制两种交替且不同的速率趋于同一极限，矛盾。故一般有聚点历史仅由定理20.8保证 AC 实现；光滑实现还须相容的各阶导数或更强光滑拓扑中的紧闭条件。$\square$

## 21. 同源双端口的内部钟与容量反演

**假设 21.1（固定制备、共同时间与认证读出）。** 令

$$
M_r=\operatorname{diag}(1,r,1),\qquad
L=\begin{pmatrix}1&-1&0\\-1&2&-1\\0&-1&1\end{pmatrix},
\qquad
S_{M_r}(t)=e^{-tM_r^{-1}L},\qquad r>0.
$$

初态位移为 $e_1$，或经已认证的配对制备与相减取得同一位移响应。两个线性读出作用于同一个状态：

$$
u(t)=(e_1-e_3)^{\mathsf T}S_{M_r}(t)e_1=e^{-t},
$$

$$
v(t)=e_1^{\mathsf T}S_{M_r}(t)e_1=k_r(t)
=\frac1{r+2}+\frac12e^{-t}
+\frac{r}{2(r+2)}e^{-(1+2/r)t}.
\tag{21.101}
$$

第一式也由 $(e_1-e_3)^{\mathsf T}M_r^{-1}L=(e_1-e_3)^{\mathsf T}$ 直接核对；其特征衰减率 $1$ 不依赖 $r$。这里的内部时间单位由单位边权和两个单位端点容量决定。若实际导纳整体为 $\kappa L$，而 $\kappa>0$ 未知，则 $-\log u=\kappa t_{\mathrm{external}}$：取得的是尺度乘外部经过时间，不能分离这两个量，也不能认定外部物理秒已校准。

两个通道可以有不同但各自保持不变的未知正增益：

$$
Y_u(s)=g_u e^{-\phi(s)},\qquad
Y_v(s)=g_v k_r(\phi(s)),\qquad g_u,g_v>0.
\tag{21.102}
$$

共同钟满足 $\phi(0)=0$，严格递增；在同一正标签 $s_*>0$ 读取时，两个通道必须对应同一实际经过时间 $t=\phi(s_*)>0$。不要求钟率已知。单点结论不需要钟函数可微；既有光滑无界钟类当然包含在适用范围内。

真实零时刻给 $Y_u(0)=g_u,\ Y_v(0)=g_v$，从而

$$
u=\frac{Y_u(s_*)}{Y_u(0)},\qquad
v=\frac{Y_v(s_*)}{Y_v(0)}.
\tag{21.103}
$$

因此“一个正时刻读数对”是两个额外标量读出，另需各通道的真实零点校准或已认证同源增益。若两个通道共享同一已认证增益，可以复用相应校准；否则不能用一个通道的零点值替另一个通道校准。

$g_u$ 的标量模型还要求整个线性泛函 $(e_1-e_3)^{\mathsf T}$ 已被认证。若用两个独立传感器相减实现它，必须先校准相对权重；$e_1$ 初态在第三坐标的零点值为零，该次零点读取不能校准第三传感器的增益。未经相对校准的差分不能当作(21.102)中的 $g_u u$。

增益漂移、未知加性基线、未建模的后续强迫、不同初态、不同来源或读出扰动均不在(21.102)内。配对制备必须认证相同生成元、相同实际延迟和同一初始位移；两个独立实验拥有相同显示标签并不自动证明这些关系。若两次读出会改变状态，须另行取得同一状态的合法联合读出，或认证等价的配对协议。

这里消去的是共同自由演化时间参数。若实际制备使用外部脉冲，脉冲幅度、输入测度与钟变换的强迫密度因子仍须满足既有运输合同；两个自由演化读出的关系不自动认证这些输入合同。

**定理 21.2（源参数与内部时间的开楔形坐标）。** 在假设21.1下，一个正时刻的已校准同刻读数对唯一恢复 $r>0$ 与该次内部时间 $t>0$，并给下述开楔形的光滑坐标。证明。应用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理19.2、19.3的核单调性与逆稳定结果。

消去 $t=-\log u$，得到

$$
\boxed{
v=G_r(u):=\frac1{r+2}+\frac u2
+\frac{r}{2(r+2)}u^{1+2/r},
\qquad 0<u<1.}
\tag{21.104}
$$

因此同一未知非线性钟的具体形式从这一个同刻关系中消去。直接求 $u$ 导数，以及把既有 $\partial_r k_r(t)$ 公式代入 $t=-\log u$，给

$$
\boxed{\partial_uG_r(u)=\frac{1+u^{2/r}}2\in(1/2,1),}
\tag{21.105}
$$

$$
\boxed{
\partial_rG_r(u)
=-\frac{H((1+2/r)(-\log u))}{(r+2)^2}<0,
\qquad H(w)=1-(1+w)e^{-w}.}
\tag{21.106}
$$

这里 $H$ 就是恢复几何卷第19节中的 $h$，换字母仅为避免混同采样间隔。对 $w>0$，$H(w)>0$，且 $H'(w)=we^{-w}>0$。

恢复几何卷定理19.2的端点极限直接成为

$$
\lim_{r\to\infty}G_r(u)=u,\qquad
\lim_{r\downarrow0}G_r(u)=\frac{1+u}{2}.
\tag{21.107}
$$

连续严格反单调性表明，固定 $u\in(0,1)$ 时，$r\mapsto G_r(u)$ 恰把 $(0,\infty)$ 一一映到 $(u,(1+u)/2)$。所以

$$
\boxed{
(r,t)\in(0,\infty)^2
\longmapsto (e^{-t},k_r(t))
}
$$

恰为

$$
\boxed{\mathcal W=\{(u,v):0<u<1,\ u<v<(1+u)/2\}}
\tag{21.108}
$$

的一一参数化。逆像由 $t=-\log u$ 和唯一方程 $G_r(u)=v$ 确定。前向映射光滑，Jacobian 为

$$
\det\frac{\partial(u,v)}{\partial(r,t)}
=u\,\partial_rG_r(u)<0.
$$

直接应用通常的局部反函数定理，并利用已得的全局单射与满射，逆映射在整个 $\mathcal W$ 上光滑。这里的 $\mathcal W$ 是精确的开区域；边界 $v=u$、$v=(1+u)/2$ 分别对应 $r\to\infty$、$r\downarrow0$，不能解释为有限正质量参数。

$t=0$ 时两值同为 $1$，只承担校准而不识别 $r$。$u=0$ 对应无限经过时间极限，不属于一次有限正时刻的读数合同。

**命题 21.3（单个内时点不恢复钟的间隙）。** 第一通道单独对 $r$ 完全不敏感，却给出 $t=-\log u$。第二通道因而成为已知内部时间的核读数，直接进入原有单调反演。参数盲通道的作用是约束另一个通道中的未知时间；没有声称它单独新增了关于 $r$ 的信息。

一个读数对不确定采样之间的钟函数。例如，固定读出标签 $s_*>0$ 和所得 $t>0$，令 $\alpha=t/s_*$，取非零 $\psi\in C_c^\infty((0,s_*))$。当

$$
|\varepsilon|\,\|\psi'\|_\infty<\alpha
$$

时，

$$
\phi_\varepsilon(s)=\alpha s+\varepsilon\psi(s)
$$

都是严格递增、光滑、无界的钟，满足 $\phi_\varepsilon(0)=0$、$\phi_\varepsilon(s_*)=t$，却在采样之间不同。钟率、钟加速度及完整钟函数没有被该单点结论识别。

**定理 21.4（参数与时间的不同稳定常数）。** 现在把真实参数和该次真实读数限制在已认证范围

$$
0<\ell\le r\le R<\infty,\qquad
0<u_{\min}\le u\le u_{\max}<1.
\tag{21.109}
$$

这些是有效的参数/取得约束，不能仅因把观测值截入区间就宣称真实值满足它们。假设同一误差事件上有

$$
|\widehat u-u|\le\delta_u,\qquad
|\widehat v-v|\le\delta_v.
\tag{21.110}
$$

先取

$$
\widetilde u=\operatorname{proj}_{[u_{\min},u_{\max}]}(\widehat u),
\qquad
J(\widetilde u)=[G_R(\widetilde u),G_\ell(\widetilde u)],
$$

$$
\widetilde v=\operatorname{proj}_{J(\widetilde u)}(\widehat v).
$$

令 $\widehat r\in[\ell,R]$ 满足

$$
G_{\widehat r}(\widetilde u)=\widetilde v,\qquad
\widehat t=-\log\widetilde u.
\tag{21.111}
$$

存在唯一逆像；$\ell=R$ 时参数本来已知，直接取该值即可。

由(21.106)及 $H$ 单调性，整个矩形上的参数灵敏度下界为

$$
\boxed{
m=\frac{H((1+2/R)(-\log u_{\max}))}{(R+2)^2}>0.}
\tag{21.112}
$$

它正是在角点 $(R,u_{\max})$ 取得的最小灵敏度。类似地，(21.105)给

$$
L_u=\frac{1+u_{\max}^{2/R}}2<1,\qquad
|\partial_uG_r(u)|\le L_u.
$$

投影不增加 $\widetilde u$ 到真实 $u$ 的距离，因此 $|\widetilde u-u|\le\delta_u$。关键是用 $G_r(\widetilde u)\in J(\widetilde u)$ 作为第二次投影的比较点：

$$
\begin{aligned}
|\widetilde v-G_r(\widetilde u)|
&\le|\widehat v-G_r(\widetilde u)|\\
&\le\delta_v+|G_r(u)-G_r(\widetilde u)|\\
&\le\delta_v+L_u\delta_u.
\end{aligned}
$$

直接复用恢复几何卷定理19.3的导数下界/差商界，得到

$$
\boxed{
|\widehat r-r|
\le\frac{L_u\delta_u+\delta_v}{m}
\le\frac{\delta_u+\delta_v}{m}.}
\tag{21.113}
$$

参数误差界成立，并可使用这里稍紧的 $L_u<1$。若数值求根仅认证了额外核残差 $\eta$，则(21.113)的分子另加 $\eta$，沿用恢复几何卷定理19.3的误差规则。

时间误差是独立的一项：

$$
\boxed{
|\widehat t-t|
\le\frac{|\widetilde u-u|}{u_{\min}}
\le\frac{\delta_u}{u_{\min}}.}
\tag{21.114}
$$

直接用 $G_r(u)$ 处理参数反演，避免了把时间误差的 $1/u_{\min}$ 因子再无谓地加进(21.113)；但恢复时间本身仍必须承担它。若要报告两项绝对误差之和，可把(21.113)与(21.114)相加。

本结论没有全域统一常数：$u_{\max}\uparrow1$ 时参数灵敏度消失；没有有限 $R$ 时同样失去参数逆稳定。另一方面，(21.112)的 $m$ 和 $L_u$ 都不依赖 $u_{\min}$。保持 $u_{\max}<1$ 与 $[\ell,R]$ 固定而令 $u_{\min}\downarrow0$，不会破坏(21.113)的参数稳定常数；失去统一稳定性的是(21.114)中的内部时间恢复。这两个条件数不能混同。$u=0$ 本身仍是无限经过时间极限，不能称为一次有限时刻可取得的读数。

**命题 21.5（投影估计不保证原始残差）。** 第二次投影依赖已经改动的横坐标 $\widetilde u$。真实 $v=G_r(u)$ 不一定属于 $J(\widetilde u)$，所以不能声称该投影单独不增加到真实 $v$ 的误差。

一个精确例子：真实 $r=2$、$u=1/2$、$v=9/16$，取参数区间 $[1,2]$、读数区间 $[2/5,4/5]$，观测为

$$
\widehat u=3/5,\quad\delta_u=1/10,\qquad
\widehat v=9/16,\quad\delta_v=0.
$$

因为 $G_2(w)=(1+w)^2/4$，投影输出

$$
\widetilde u=3/5,\qquad
\widetilde v=G_2(3/5)=16/25,\qquad
\widehat r=2.
$$

于是

$$
|\widetilde v-\widehat v|=31/400>0=\delta_v.
$$

它仍满足(21.113)–(21.114)，但预测的同刻读数对不满足原来的第二条零误差残差。若交付要求一份与全部已获记录相容的模型，必须另验同一个候选满足原始两条残差及旧档案；不能把这里的投影操作称为该共同可行性的证书。

**命题 21.6（四个原始读数的共同误差）。** 沿用恢复几何卷第19节的比值误差界。设每个通道的真实零点及当前读数分别为 $g_u,g_uu$ 和 $g_v,g_vv$，四条已认证原始误差为 $\epsilon_{u0},\epsilon_{us},\epsilon_{v0},\epsilon_{vs}$。若观测零点满足

$$
\widehat Y_{u0}>\epsilon_{u0},\qquad
\widehat Y_{v0}>\epsilon_{v0},
$$

则归一化观测可取

$$
\widehat u=\widehat Y_{us}/\widehat Y_{u0},\qquad
\widehat v=\widehat Y_{vs}/\widehat Y_{v0},
$$

$$
\delta_u=
\frac{\epsilon_{us}+\epsilon_{u0}}{\widehat Y_{u0}},
\qquad
\delta_v=
\frac{\epsilon_{vs}+\epsilon_{v0}}{\widehat Y_{v0}}.
\tag{21.115}
$$

这里只用 $0<u,v<1$ 和
$(\widehat Y_{us}-u\widehat Y_{u0})/\widehat Y_{u0}$ 的恒等式，另一通道同理。两通道和零点的误差可以相关；预算必须在同一联合事件上成立，不能把共享校准误差另当独立抽样。若读数来自配对差分，相应制备与差分误差先进入这些原始界。没有安全正分母或增益下界时，不存在这种统一绝对噪声保证。

若要求一份原始仪器记录的合法拟合，应保留同一个 $(r,t,g_u,g_v)$ 的四个残差，而不只保留式（21.115）的两个外包半径。例如默认误差盒的精确候选集为
$$
\begin{aligned}
\mathcal F_Y=\{(r,t,g_u,g_v):\;&r,t,g_u,g_v>0,\\
&|g_u-\widehat Y_{u0}|\le\epsilon_{u0},\quad
|g_u e^{-t}-\widehat Y_{us}|\le\epsilon_{us},\\
&|g_v-\widehat Y_{v0}|\le\epsilon_{v0},\quad
|g_vk_r(t)-\widehat Y_{vs}|\le\epsilon_{vs},\\
&\text{同一来源、钟、校准与全部旧档案相容}\}.
\end{aligned}
\tag{21.116}
$$
已知更小的联合误差集时，四个盒条件换成同一个原始残差向量属于该集；两个归一化区间分别非空不证明 $\mathcal F_Y$ 非空。假设21.1的共同时间、实际读出泛函及制备条件也始终保留。

**命题 21.7（增益、读出泛函、同刻与制备的必要性见证）。** **没有增益校准。** 即使两个通道共享一个未知正增益 $g$，单个原始正读数对仍可对 $r$ 完全不识别。给定任意 $0<U<V$，设 $\rho=V/U>1$。对每个 $r>0$，

$$
e^tk_r(t)=\frac{e^t}{r+2}+\frac12
+\frac{r}{2(r+2)}e^{-2t/r}
$$

从 $1$ 严格增至无穷，其导数为

$$
\frac{e^t-e^{-2t/r}}{r+2}>0\quad(t>0).
$$

因此存在 $t_r>0$ 使 $e^{t_r}k_r(t_r)=\rho$，再置 $g_r=Ue^{t_r}$，每个 $r>0$ 都产生同一原始读数对 $(U,V)$。不同未校准增益只会引入更多自由度。

即使两个输出零点都为 $1$，差分端口的相对权重也可能错。真实 $r=2,t=\log2$ 时，两个端点状态值为 $9/16,1/16$。若仪器实际相减的是第一坐标减去两倍第三坐标，会报告 $(u,v)=(7/16,9/16)$，其零点读数仍均为 $1$。该对位于开楔形内，却有 $G_2(7/16)=529/1024\ne9/16$，会把内部时间和参数都识别错。这属于未认证读出泛函，不能由标量零点归一化补救。

**两个通道没有共同经过时间。** 若实际为 $u=e^{-t_u}$、$v=k_r(t_v)$，则第一值只确定 $t_u$。例如固定已归一化对 $(u,v)=(1/2,9/16)$：对每个 $r>0$，因 $p_r<1/2<9/16<1$，均可取 $t_v=k_r^{-1}(9/16)$，同时取 $t_u=\log2$。两个不同的线性钟已足以在同一显示标签产生这些值。真实零点和增益校准都不能替代共同时间关系。

**初态来源不对，即使零点读数都正确也会误判。** 真实参数取 $r=2$，实际初态却为

$$
w=e_1+\frac19e_2.
$$

两通道在真实零点仍均读 $1$。中点初态的端点传递为

$$
e_1^{\mathsf T}S_{M_r}(t)e_2
=\frac{r}{r+2}\bigl(1-e^{-(1+2/r)t}\bigr),
$$

而它对差分端口的贡献为零。因此在 $t=\log2$ 时，

$$
u=1/2,\qquad
v=\frac9{16}+\frac19\frac38
=\frac{29}{48}=G_1(1/2).
$$

同一时刻、正确的两个零点值、位于开楔形内部的读数对，却与“初态 $e_1$、参数 $r=1$”完全相同。单对读数不能认证初态来源。未建模强迫或读出导致的状态扰动同样不能由同刻标签排除。

**显示零点不是真实制备零点。** 真实 $r=2$，显示零点落在真实 $b=\log2$，再过 $t=\log2$ 读取并分别除以显示零点值。差分端口给 $u=e^{-t}=1/2$，但端点通道给

$$
v=\frac{k_2(2\log2)}{k_2(\log2)}
=\frac{25/64}{9/16}
=\frac{25}{36}.
$$

该对仍位于开楔形内部，却不是 $G_2(1/2)=9/16$。强行使用(21.104)会得到另一个参数。差分端口能正确给出这段时间增量，不代表端点通道已取得正确的增益归一化。

这些反例均由所列恒等式成立。它们说明新桥所需的是实际共同关系：固定来源、合法初态、真实零点、稳定增益、已认证读出泛函和同一状态/经过时间。新增读出与旧档案共同约束模型，不替换已经取得的其他记录。

在上述同源制备和校准假设下，定理21.2使用一个正时刻的两个通道，[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理20.2使用从零开始的五个等步单端口值；前者允许未知共同非线性钟，后者要求未知正线性钟。这是不同取得合同下的两种充分关系，不能由读数个数推出费用优劣。合法通道、准备、校准、等待、存储及算术各有费用，仍须分别计量。

## 22. 推进操作、输入测度与谱记忆的钟运输

**定理 22.1（一维时变系统的任意阶标签 Hankel 秩）。** 下列同一个一维系统经已知非线性钟重标后，普通等步标签读数具有任意大的 Hankel 秩；其正确强迫接口和物理变换仍可运输。证明。

先固定同一个物理系统

$$
\dot x(t)=-x(t)+u(t),\qquad y(t)=x(t).
$$

零输入、已制备初态 x(0)=1 的完整响应为 K(t)=e^{-t}。其物理时间离散序列 e^{-n} 的所有非空 Hankel 块都秩一。

取已知钟 t=φ(τ)=log(1+τ)。它光滑、φ(0)=0、φ′(τ)=1/(1+τ)>0，且趋于无穷。实际重标曲线为

$$
k(\tau)=K(\phi(\tau))=\frac1{1+\tau}
=\int_0^\infty e^{-\lambda}e^{-\lambda\tau}\,d\lambda.
$$

最后等式是直接积分；这是标记曲线的一个连续正谱表示。它不可能写成有限正原子和 Σ_j w_j e^{-λ_j τ}，其中 w_j>0、λ_j≥0：有零率原子就有非零平台；没有零率原子时，有限集合的最小率 λ_min>0 给指数上界 (Σw_j)e^{-λ_min τ}，与 1/(1+τ) 的尾部矛盾。这只排除指定的有限正谱类，不把“连续谱表示”直接认作原系统的物理隐藏状态。

更强且只用实际离散读数的下界为

$$
H_N(i,j)=k(i+j)=\frac1{i+j+1}=\int_0^1 z^{i+j}\,dz,
\qquad 0\le i,j<N.
$$

任意非零 a∈R^N 给非零多项式 P(z)=Σ_i a_i z^i。P 不会在整个 (0,1) 恒为零；连续性给一个区间上 P²>0。因此

$$
a^T H_Na=\int_0^1P(z)^2\,dz>0.
$$

故 rank H_N=N。应用 `HankelRankMinimality.finiteHankel_eq_observability_comp_controllability`，任意 d 维线性时不变实现的 Hankel 块由观测矩阵乘可达矩阵分解，秩≤d；取 N=d+1 即矛盾。所以整个序列 k(n) 没有有限维 LTI 实现。只取得前 2N−1 个精确读数时，能推出的是任何与该前缀匹配的 LTI 实现维数至少 N；有限 N 不证明原物理系统有无限状态。

原系统仍有一个动态状态。 令 X(τ)=x(φ(τ))、v(τ)=u(φ(τ))，合法运输得到

$$
X'(\tau)=\frac{-X(\tau)+v(\tau)}{1+\tau}.
$$

这是一维时变实现。若要求自主形式，可增加已知钟态 r′=1、r(0)=1，写 X′=(-X+v)/r；它是二维自主非线性控制系统，不是有限维 LTI 实现。两种维数陈述的模型类不同。

继续比较同一个强迫协议。 零初态时，保留 力值 输入 v=u∘φ，换元给

$$
X(\tau)=\int_0^\tau
 e^{-(\phi(\tau)-\phi(\sigma))}\phi'(\sigma)v(\sigma)\,d\sigma
=\int_0^\tau\frac{v(\sigma)}{1+\tau}\,d\sigma.
$$

这里是两时接口的核；本例中的 σ 依赖恰好相消。它仍不是 k(τ−σ)。取合法有限矩形输入 v=1_[1,2]，即物理 u=1_[log 2,log 3]。在 τ=2，真实输出为 1/3；误把初态曲线当新卷积核则给

$$
\int_1^2 k(2-\sigma)\,d\sigma=\log 2.
$$

这不是分布脉冲，也没有改变比较中的输入或初态。若改用输入密度 w(σ)=φ′(σ)u(φ(σ))，则积分核相应为 (1+σ)/(1+τ)。两种输入约定各自成立，不可混用。

积分与频域条件同样运输。 原 ∫K(t)dt=1；新 ∫k(τ)dτ 发散；保留物理测度则

$$
\int_0^\infty k(\tau)\phi'(\tau)\,d\tau=1.
$$

因此不能把物理核的 L1 小增益合同直接移给 k(τ−σ)。普通未阻尼 Fourier 变换的绝对可积前提也不能直接移过来；这里不排除个别非零频率的条件收敛。保留正确相位与测度时，物理 Fourier 响应仍为

$$
\int_0^\infty e^{-i\omega\phi(\tau)}k(\tau)\phi'(\tau)d\tau
=\frac1{1+i\omega}.
$$

**命题 22.2（共同有界钟率下的物理谱歧义）。** 定理22.1的 φ′ 没有正的统一下界。下面的同一缺口在共同双边钟率合同内仍出现，首先给出有限秩一与二的区别。

令 U=R。两个物理正实现为

$$
C_A=1,\quad J_A=1,\quad K_A(t)=e^{-t};
\qquad
C_B=\operatorname{diag}(1,2),\quad
J_B=(1/\sqrt2,1/\sqrt2)^T,\quad
K_B(s)=\tfrac12(e^{-s}+e^{-2s}).
$$

均满足 K=J*e^{-tC}J；初态制备 x(0)=J1、输出 J*x 给相应零输入响应。两者初始输出都为 1，谱都在共同区间 [1,2]。

在 A 使用未知钟

$$
\phi(s)=-\log K_B(s)
=s+\log2-\log(1+e^{-s}),
$$

在 B 使用恒等钟。直接求导得

$$
\phi'(s)=\frac{1+2e^{-s}}{1+e^{-s}}\in(1,3/2],\quad
\phi(0)=0,\quad \phi(s)\to\infty.
$$

所以两种钟均满足共同合同 1≤钟率≤3/2，且完整标记响应逐点相等：K_A(φ(s))=K_B(s)。本例连无穷尾部都相同，两者平台都为零，因此不与 本卷命题18.6 的特定非零平台识别矛盾。

取任意 h>0，令 x=e^{-h}、z=e^{-2h}，共同数据 a_n=(x^n+z^n)/2 给

$$
a_0a_2-a_1^2=\tfrac14(x-z)^2>0.
$$

由 Hankel 因子化，B 的物理最小 LTI 维数至少 2，而展示的实现给上界 2；A 的物理最小维数为 1。`FinitePronyHankelReconstruction.prony_hankel_rank` 也直接给共同标记序列的秩 2。

物理时间 Laplace 目标同样不同：对 p>0，

$$
\widehat K_A(p)=\frac1{p+1},\qquad
\widehat K_B(p)=\frac1{2(p+1)}+\frac1{2(p+2)}.
$$

在 p=1 分别为 1/2 与 5/12。因此观察对象只包含完整标记曲线及上述共同谱界/钟率界时，物理最小维数和物理 Laplace 响应都不在观察纤维上恒定。所有后处理，包括精确求标记曲线的 Fourier/Laplace 变换，都不能将这两个世界分开。

这个反例不需要固定正幅度的钟率不确定性。将第二率改成 1+δ，δ>0，并令 φ=-log[(e^{-s}+e^{-(1+δ)s})/2]，则 1<φ′≤1+δ/2；对任意 ε>0，选 δ≤min(1,2ε)，仍有秩 1/2 歧义而钟率落在 [1,1+ε]。这不涵盖 ε=0。

同一构造覆盖任意有限正谱族。给定 F(s)=Σ_j w_j e^{-λ_j s}，w_j>0、Σw_j=1、λ_j>0，取 λ_0>0，令 φ(s)=-log F(s)/λ_0 及倾斜权重 π_j(s)=w_j e^{-λ_j s}/F(s)。则

$$
F=e^{-\lambda_0\phi},\qquad
\phi'=\frac{\sum_j\pi_j\lambda_j}{\lambda_0}
\in[\lambda_{\min}/\lambda_0,\lambda_{\max}/\lambda_0],
\qquad
\phi''=-\frac{\operatorname{Var}_{\pi(s)}(\lambda)}{\lambda_0}\le0.
$$

证明为 F′/F 的直接微分：π_j′=π_j(Σ_kπ_kλ_k−λ_j)，代回即给负方差。正率还给 φ(0)=0 与 φ→∞。故允许这些未知钟时，任意有限谱复杂度都能吸收到单模的钟里。给定先验钟率 [m,M] 时仍须核实本例实际 φ′ 位于该区间；上述端点界是充分条件，不声称任意谱自动适配任意先验。特别，对任意 ε>0 和任意整数 $N\ge2$，可以选 N 个互异 λ_j∈[1,1+min(ε,1)]、λ_0=1 与正归一化权重，得到共同钟率 [1,1+ε]、共同物理谱界 [1,2] 下的维数 1/N 歧义。这是标准 log-sum-exp 导数恒等式与既有 Prony 秩定理的组合，不是新的对数配分函数理论。

限制：比较的是完整零输入初态响应，不是所有驱动实验的等价。若档案已有各物理采样时刻、校准钟、能区分的输入实验或与物理时间绑定的实际费用读数，这些资料必须并入观察 Q；上述两个世界未被证明在扩大的 Q 下仍相同。不能删掉档案来制造碰撞。

**命题 22.3（记录核、推进交织与实际费用）。** 对已知、共同、连续严格递增且满射的 $\phi:[0,\infty)\to[0,\infty)$，定义 R_φf=f∘φ。它在完整函数空间上可逆。任意记录映射 Q 都有

$$
R_\phi Q(x)=R_\phi Q(y)\iff Q(x)=Q(y).
$$

因此仅改记录坐标不改变观察核，也不改变“目标在每条观察纤维上恒定”的准确可恢复性。命题22.2变粗的是**未知钟也属于待识别对象**时的观察映射；不同对象使用不同 φ，不能用一个共同已知的逆变换撤回。

然而物理平移 S_hf(t)=f(t+h) 在重标记录上的运输是

$$
(\widetilde S_hF)(s)
=F\bigl(\phi^{-1}(\phi(s)+h)\bigr),
\qquad
R_\phi S_h=\widetilde S_hR_\phi.
$$

这正是 `BehaviorCompletionTranslation.behavior_completion_translation` 所需的交织条件。对单模的 F=e^{-φ(s)}，有 S̃_hF=e^{-h}F，运输后的闭合仍一维。普通标签平移 F(s+h) 则在定理22.1给无限维平移闭合，在命题22.2给二维。将 S̃_h 换成普通平移，不再是 `DynamicClosureMinimality.dynamic_closure_is_least` 中相同的干预族。

再假设 $\phi$ 为 $C^1$ 且 $\phi'>0$，物理 Laplace 的合法计算为

$$
\widehat K(p)=\int_0^\infty
 e^{-p\phi(s)}K(\phi(s))\phi'(s)\,ds.
$$

普通标签变换 ∫e^{-ps}K(φ(s))ds 是另一个目标。仿射 φ(s)=cs 才有熟悉的 $\mathcal L[K(c\,\cdot)](p)=c^{-1}\widehat K(p/c)$。Fourier 同样必须运输相位及测度；完整数据的单射编码与目标运算闭合是分开的条件，正如[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)定理31.15 已证明的代数观察现象。

有限取得时只有原样点会被重标。新钟等步点一般不是已有物理等步点；从有限向量做可逆 DFT 保留该向量的核，但不给未测的点、整个响应、导数或无穷极限。连续 Laplace/Fourier 积分不是这个有限 DFT 所附赠的接口。

[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)命题4.7 精确说明有限宏读数如何回到同一原始记录：p=B^Tz，宏系数 u 实际展开为 Bu，盒噪声幅度为 ε||Bu||_{1,σ}。共享原始噪声的变换系数不能被重新宣布独立；已支付的取得费用也不因表达变短而退款。本卷定理12.7 对真实重标保留点操作费用，连续费率乘 φ′；命题22.2若把物理钟费用加入 Q，就必须重新检验同纤维条件。

## 23. 可读模态的相位幅度钟与素数参照

**定义 23.1（闭合模态接口）。** 给集合 X 与作用 T_t:X→X（t≥0），满足 T_0=id、T_{t+s}=T_tT_s。给定 $N\ge1$ 个复值可读函数 χ_j:X→ℂ 和已知复数 s_j，满足

$$
\chi_j(T_t x)=e^{s_jt}\chi_j(x)\qquad(t\ge0,x\in X).
\tag{23.101}
$$

记 Ψ(x)=(χ_j(x))_{j=1}^N，并以 y(x)=Σ_jχ_j(x) 为指定标量读出。可读意味着当前协议允许取得该值，或已给出从现有合法记录恢复它的映射与条件；式(23.101)本身不授予访问权限。一般系统也不自动存在这样一组有限模态。写 s_j=−γ_j+iω_j 只是在此闭合模型内拆分生成元，不是概率或物理假设。

**命题 23.2（当前模态与指定未来响应的闭合）。** 有

$$
\Psi(T_t x)=\operatorname{diag}(e^{s_1t},\ldots,e^{s_Nt})\Psi(x),
\qquad y(T_t x)=\sum_j e^{s_jt}\chi_j(x).
\tag{23.102}
$$

所以 Ψ 相等的两个状态具有相同的全部 y 未来。若存在 h>0 使 m_j=e^{s_jh} 互异，则相同的前 N 个 h 间隔 y 读数也强制 Ψ 相等。因此该有限窗口、Ψ 和全部 y 未来在 X 上具有同一个观察核。

**证明。** 前式逐坐标就是(23.101)，求和给后式。窗口是 VΨ，其中 V_{nj}=m_j^n、0≤n<N。节点互异，直接应用已有 Vandermonde 窗口单射性，即`FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective` 的复数实例。全部未来包含该窗口，所以三个核相等。此论证恢复的是指定模态任务商；除非另证 Ψ 对 X 单射，不恢复全部微观状态。□

复数 s_j 互异不保证采样节点 m_j 互异。纯衰减实率互异在任意 h>0 下给互异节点；含相位时还须排除相差 2πik/h 的率。

**定义 23.3（同源非零衰减模态记录）。** 固定 x∈X、一个满足(23.101)的模态 χ，令 s=−γ+iω、γ>0、χ(x)≠0。标签区间 I 含初始点 τ_0，φ:I→[0,∞) 连续严格递增，φ(τ_0)=0；实际记录为

$$
Z(\tau)=g\,\chi(T_{\phi(\tau)}x),\qquad g\in\mathbb C\setminus\{0\}
\tag{23.103}
$$

且 g 在该记录内固定。它可以未知，因为以下比值使用同一个传感器的实际初始记录 Z_0=Z(τ_0)。不允许任意时间变增益、遗漏初始记录或把两来源记录拼作同一模态。

定义 A(τ)=|Z(τ)|、a(τ)=−log[A(τ)/A(τ_0)]。令 θ 是 Z/|Z| 的连续实相位提升，初值 θ(τ_0)已固定。相位提升是完整连续非零轨迹的数学对象；它是否实际可得须另外由连续记录或已认证的绕数信息保证。

**命题 23.4（共同钟消去及尺度边界）。** 对所有 τ∈I，

$$
a(\tau)=\gamma\phi(\tau),\qquad
\theta(\tau)-\theta(\tau_0)=\omega\phi(\tau)
=\frac\omega\gamma a(\tau).
\tag{23.104}
$$

若 φ 可微且 φ′>0，则局部衰减率 a′=γφ′ 与相位率 θ′=ωφ′ 同乘换钟因子；其比为 ω/γ。任何两个幅度相差二倍的已记录点之间，连续累计相位差为 (ω/γ)log2。若 γ已知，则幅度给相对内部时间 φ=a/γ；若 γ未知，(γ,ω,φ)→(cγ,cω,φ/c)、c>0 保持全部 Z，不识别绝对率与绝对时间单位。

**证明。** 由(23.101)，Z/Z_0=e^{(−γ+iω)φ}，取模和实对数得第一式。函数 θ_0+ωφ 是相应单位相位的一份连续提升；任意同初值提升与它的差属于2πℤ且连续，在区间上必恒为零，故得第二式。求导给局部公式；两点 a 差等于log2给半幅公式。最后直接代入尺度变换。□

γ=0 时幅度恒定，不能充当这一内部钟；χ(x)=0 时整个模态不可见；只有 |Z| 时 ω完全不可见。任意混合读出 Σχ_j 的相位与模长也不满足(23.104)，除非另证它自身是一份非零模态。常数增益能由同源比值消去不意味着时变增益也能消去。

若传感器只读强度 |Z|²，对数比为2γφ，应保留因子2；只读实部也不提供复相位。相位方向的坐标约定须固定，未知复共轭会留下ω/γ与−ω/γ的歧义。反过来，观察到(23.104)形式也不单独认证一模来源：任意严格正的实混合衰减都有恒定相位和零斜率，仍须保留已声明模态类及共同来源条件。

“周期”在此只指纯相位因子的一次闭合；γ>0 的完整 Z 轨迹不具有正周期。半幅不是概率半衰或熵变化。[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第127.13节的热流/波动比较已经承担两种演化规则的区别，此处保留该区别。

**推论 23.5（参照模态确定相对谱图）。** 在定义23.1的同一系统、同一 x、同一未知 φ 下，另有一个合法可读参照模态 ζ，满足 ζ(T_t x)=e^{(−γ_*+iω_*)t}ζ(x)、γ_*>0、ζ(x)≠0。令

$$
u(\tau)=\frac{|\zeta(T_{\phi(\tau)}x)|}{|\zeta(x)|}\in(0,1],
\qquad a_*(\tau)=-\log u(\tau).
$$

则每个选定模态满足

$$
\chi_j(T_{\phi(\tau)}x)
=\chi_j(x)\exp\!\left[-\frac{s_j}{\gamma_*}\log u(\tau)\right].
\tag{23.105}
$$

因此消去未知共同标签后，记录落在由初始模态与相对率 s_j/γ_* 确定的一张图上。

**证明。** 命题23.4给 φ=−log u/γ_*，代入(23.101)。u>0，所以这里使用唯一实对数，不涉及复对数选支。□

若连续相位和非零初值的各个模态确已可读，可以由各模态的对数幅度、展开相位相对于 a_* 的斜率恢复相对率；这只是(23.104)逐模态应用。单个标量混合响应没有免费提供这些独立通道。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)引理15.8的单调共享迹是另一种内部钟，不须把正谱混合迹错误拆成已取得的每个模态。

**命题 23.6（校准素数热坐标与未知尺度纤维）。** 使用 `PrimeZeckendorfFrequencyBridge.first_excited_prime_frequency` 的既有 $\lambda_p=\varphi^2\log p$（第一激发层），以及 `PrimeGoldenComplexMode.first_golden_complex_mode_euler` 和模长公式。这里不重证一般素数对数独立性；读数也不恢复该频率所忽略的层坐标。

令 $\varphi=(1+\sqrt5)/2$ 为黄金比，$c=\varphi^2>0$、$\lambda_p=c\log p$，其中p为素数，故λ_p>0。定义
$$
A_p(\sigma)=e^{-\sigma\lambda_p},\qquad
M_p(\sigma,t)=e^{-\sigma\lambda_p}e^{it\lambda_p}.
$$
若σ>0已知，精确合法幅度A=A_p(σ)唯一确定
$$
\boxed{p=\exp\!\left(\frac{-\log A}{c\sigma}\right).}
\tag{23.111}
$$
所以完整复读数也确定p，而无需先解相位绕数。若σ作为未知参数可取任意正数，则对任意两个素数p,q，置
$$
\sigma_q=\sigma_p\frac{\log p}{\log q}>0
$$
就有A_q(σ_q)=A_p(σ_p)。联合观测(p,σ)↦A因此不单射。

**证明。** 取实对数给−log A=cσlog p，除以正cσ并取指数得到(23.111)；这等价于 `PrimeZeckendorfTemporalization.first_excited_heat_multiplier_injective` 的正热坐标单射性。碰撞直接由σ_q log q=σ_p log p得到。对于复读数，进一步取 $t_q=t_p\log p/\log q$ 即保证完整 $M$ 也相同；固定已知t时，不可仅凭幅度碰撞断言复读数相同。□

(23.111)以数据确属所声明素数模态类为前提；任意带噪A代入后得到的正实数不能自动取整为认证素数。精确单射也不提供整个无界素数集合上的统一绝对误差间隔，因为A_p(σ)随p→∞趋零。

**命题 23.7（素数模态的共同钟代入与全记录碰撞）。**

固定a>0、b∈ℝ。设h:I→[0,∞)连续严格递增，h(τ_0)=0，实际零点归一化复记录为
$$
Z_p(\tau)=M_p(a h(\tau),b h(\tau))
=\exp\!\left[(-a+ib)\lambda_p h(\tau)\right].
\tag{23.112}
$$
若θ是初值为零的连续相位提升，令L=−log|Z_p|，则
$$
L(\tau)=a\lambda_p h(\tau),\qquad
\theta(\tau)=b\lambda_p h(\tau),\qquad
\boxed{\theta=(b/a)L.}
\tag{23.113}
$$
因此任一正时间处、在相位提升可取得的条件下，θ/L只给b/a，不给p。对任意素数q，令h_q=(log p/log q)h；则同样a,b下有Z_q[h_q]=Z_p[h]，整条复记录逐点相同。

**证明。** 直接取模、实对数和显式连续相位，得(23.113)。λ_qh_q=λ_ph使(23.112)的完整指数相等。□

碰撞假设候选钟类允许这一正缩放；有额外钟率界、真实时间点或费用读数时，必须检查h_q仍满足全部旧档案。它保留的是同一**标签**记录，不宣称已校准原时间的两系统相同。有限复样本仅给相位模2π，不能免费给(23.113)中的累计θ；仅看幅度或实部更不够。若读数带未知但恒定非零复增益，可用同一传感器的真实零点读数归一化；时变增益不能这样消去。

**命题 23.8（半衰与联合熵、全流反演的两种反例）。** 对任意γ>0，以下两项同时成立。

1. 存在具有固定坐标半衰期log2/γ的二维全流，它可逆、保面积，具有明确的时间反演，并保持任意具有有限微分熵的联合概率密度之微分熵。
2. 存在两态连续时间Markov过程，其存活概率以固定半衰期log2/γ指数衰减，但两态Shannon熵先增后减。

**证明。** 第一项取
$$
\Phi_t(x,p)=(e^{-\gamma t}x,e^{\gamma t}p),\qquad t\in\mathbb R.
$$
它满足Φ_{t+s}=Φ_tΦ_s、Φ_t^{-1}=Φ_{−t}、det DΦ_t=1，且x(t+log2/γ)=x(t)/2。交换R(x,p)=(p,x)满足R²=id及RΦ_tR=Φ_{−t}，给出具体反演。若初始密度ρ≥0、积分为一、ρlogρ可积，推前密度为ρ_t=ρ∘Φ_{−t}；变量替换和Jacobian一给
$$
-\int\rho_t\log\rho_t\,dx\,dp
=-\int\rho\log\rho\,dx\,dp.
$$
这是`DifferentialEntropyChangeOfVariables` 的变量替换公式的常Jacobian特例。一个坐标的收缩由另一个坐标的扩张补偿；这里只声称联合微分熵，不将它改称热力学熵。

第二项取存活态到吸收态的跃迁率γ，后者吸收，从存活态确定初态开始。列概率满足q′=−γq、q(0)=1，所以p(t)=(q,1−q)、q=e^{−γt}。对t>0，两质量严格正，直接微分得到
$$
H'(p(t))=\gamma q(t)\log\frac{q(t)}{1-q(t)}.
$$
因此0<t<log2/γ时导数正，在该时刻为零，此后导数负；H由零升至log2再趋零，而每段长度log2/γ仍使存活概率减半。这是合法吸收Markov模型，却没有[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第127.2节要求的对称双随机生成元；故不与那里已证明的熵增冲突。□

## 24. p 进数字历史、最小闭合与相容完成

**定义 24.1（共同初态、精度与合法加一历史）。** 固定素数 $p\ge2$，以 $\mathbb Z_p$ 为 p 进整数环，$q_m:\mathbb Z_p\to\mathbb Z/p^m\mathbb Z$ 为自然投影，$m\ge0$，$q_0$ 是模一的唯一读数。$[q_m(x)]\in\{0,\ldots,p^m-1\}$ 表示规范整数代表。初始协议仅允许单位动作
$$
T(x)=x+1,\qquad T^n(x)=x+n\quad(n\in\mathbb N).
$$
所有读数不扰动状态，来自同一初态和同一条轨道。动作数、精度、传感器身份及实际结果均保留在档案。已知事件数 $n_i\in\mathbb N$、深度 $m_i$ 的实际记录为
$$
y_i=q_{m_i}(x+n_i).
\tag{24.101}
$$
若有完整旧记录 $C$，所有新增条件均与 $C^{-1}(C_{\rm actual})$ 相交。初态 $x$ 与当前态 $x+n_i$ 是不同目标，由已知事件数运输；未知事件数、起点、增量或传感器标度须列为共同未知量。数学上的所有可能历史不是实际已执行的有限历史，也不提供秒、回溯或复制许可。

使用 $d_p(x,y)=|x-y|_p$、$|p|_p=p^{-1}$，有
$$
q_m(x)=q_m(y)\iff x-y\in p^m\mathbb Z_p
\iff d_p(x,y)\le p^{-m}.
\tag{24.102}
$$
这是 p 进整数投影核与距离的标准关系，参见 Gouvêa, *p-adic Numbers: An Introduction*, 2nd ed., Springer, 1997，及 Mathlib `PadicInt.ker_toZModPow`、`ext_of_toZModPow`。仓内 `PadicBallFiberCorrespondence.modeq_iff_padic_dist_le` 的整数输入结论是它在 $\mathbb Z$ 上的特化；此处完整载体为 $\mathbb Z_p$。

**命题 24.2（有限层周期与完整态非周期）。** 对 $m\ge0$、$x\in\mathbb Z_p$、$n\ge0$，
$$
q_m(T^n x)=q_m(x)\iff p^m\mid n.
$$
每条 $q_m$ 读数序列的最小正事件周期是 $p^m$，$m=0$ 时为一。完整状态无正整数周期，$T$ 是可逆等距映射。

证明。环同态性给 $q_m(x+n)=q_m(x)+q_m(n)$，消去得相等恰当 $p^m\mid n$。完整状态若 $x+n=x$，则整数 $n$ 在 $\mathbb Z_p$ 中为零，整数嵌入单射使 $n=0$。亦可由共同周期被所有 $p^m$ 整除，再取 $p^m>n$ 得到矛盾。逆映射是 $x\mapsto x-1$，距离等式来自 $(x+1)-(y+1)=x-y$。代数可逆性不把逆动作加入定义24.1的合法协议。

所以每个有限精度存在周期，不等于存在一个对全部精度有效的共同正周期。分辨率 $p^{-m}$ 与可见事件周期 $p^m$ 的倒数关系属于此指定动作和距离规范，不是普适物理尺度律；这里没有收缩、半衰或熵产生。$\square$

**命题 24.3（合法正步抽样与代数逆步扩展）。** 若已知每次样本跨过正整数 $a\ge1$ 次加一，实际序列 $q_m(x+aj)$ 的最小正样本周期是
$$
\frac{p^m}{\gcd(p^m,a)}=p^{\max\{m-v_p(a),0\}}.
\tag{24.103}
$$
$a=0$ 单独表示不推进时的重复记录，读数恒定、周期一，不代入 $v_p(0)$。若另外明确允许合法执行 $T^{-1}$，才可把公式扩展到负整数步 $a$，此时代入 $|a|$。

证明。正步可由合法单位动作复合执行；周期 $h\ge1$ 恰满足 $p^m\mid ah$。写 $a=p^v u$ 且 $p\nmid u$，条件等价于 $p^{\max(m-v,0)}\mid h$，得到最小值。零步直接恒定；负步的同余计算相同，但其实际执行要求所述逆动作许可。未知步长可以改变读数周期，例如 $a=p^m$ 使第 $m$ 层记录恒定。换事件标签只有在运输同一实际样点时保留实验，重新等步抽样是另一协议。$\square$

**命题 24.4（固定低模读数已经动态闭合）。** 对 $m,N\ge0$，令
$$
Q_{m,N}(x)=(q_m(x),q_m(Tx),\ldots,q_m(T^Nx)).
$$
则 $\ker Q_{m,N}=\ker q_m$，全部无穷未来历史也有相同核。更一般，任意非空已知时刻集合上的同精度读数具有同一核。

证明。每个读数为 $q_m(x)+q_m(n)$，所以 $q_m$ 相等迫使所有读数相等；反向从任一已知时刻消去 $q_m(n)$。因而等待不提高初态分辨率，虽然动作档案仍增长。例如 $x$ 与 $x+p^m$ 有相同全部 $q_m$ 历史而 $q_{m+1}$ 不同。闭合接口能预测当前模态及全部未来低模值，不恢复更高位。$\square$

**定理 24.5（不同精度的共同纤维）。** 对有限非空记录（24.101），令 $K=\max_i m_i$，$z_i=y_i-q_{m_i}(n_i)$。共同候选非空，当且仅当每对 $z_i,z_j$ 在模 $p^{\min(m_i,m_j)}$ 下相同。相容时，选 $m_j=K$，令 $a=[z_j]$，则全部新记录的纤维恰为
$$
\mathcal F=a+p^K\mathbb Z_p.
\tag{24.104}
$$
完整候选仍为 $\mathcal F\cap C^{-1}(C_{\rm actual})$。

证明。共同 $x$ 的所有投影必相容，得必要性。若相容，最高精度 $z_j$ 的每个相应约化等于 $z_i$，故每个 $x\equiv a\pmod{p^K}$ 都满足记录。反之，第 $j$ 条已强制该同余。精度集非空且有有限上界时，即使记录无限，其最大精度仍在集合中，使用同一论证仍为该球。无界相容深度的情况由命题24.12给出。不同读数分别可能，不足以替代共同相容性。$\square$

**命题 24.6（没有附加先验时的锐恢复半径）。** 对式（24.104）的非空球，若全部球内初态均被允许且输出可取任意 $\mathbb Z_p$ 点，最小最坏 $d_p$ 误差恰为 $p^{-K}$，每个相容中心都达到。

证明。若 $b\in\mathcal F$，全部 $x\in\mathcal F$ 有 $|x-b|_p\le p^{-K}$，而 $x=b+p^K$ 达到等号。若 $b\notin\mathcal F$，则 $|b-a|_p>p^{-K}$，强三角关系使每个 $x\in\mathcal F$ 都满足 $|x-b|_p=|a-b|_p>p^{-K}$。故半径等于球直径，不是实线段的半直径。附加旧档案可缩小纤维，所述无先验下界不直接适用于该交集。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的纤维恢复原则可以使用，其实凸对偶与中点公式不能无条件搬到此超度量。$\square$

**定义 24.7（单个高位与固定连续协议）。** 对 $k\ge0$，令 $P=p^k$，
$$
d_k(x)=\left\lfloor\frac{[q_{k+1}(x)]}{P}\right\rfloor\in\{0,\ldots,p-1\},
\qquad [q_{k+1}(x)]=bP+r,\quad 0\le b<p,\ 0\le r<P.
$$
该传感器只读第 $k$ 位，不是完整低模 $q_k$。固定协议
$$
W_{k,N}(x)=(d_k(x),d_k(Tx),\ldots,d_k(T^Nx))
$$
使用 $N$ 次演化、$N+1$ 次实际读取，样点恰为 $0,\ldots,N$。

**定理 24.8（携带显露的精确恢复）。** 有 $\ker W_{k,P-1}=\ker q_{k+1}$。首读数给 $b$；若时刻 $1,\ldots,P-1$ 首次在 $\tau$ 观察到不同于 $b$ 的值，则 $r=P-\tau$；若无变化，则 $r=0$。因此 $P=p^k$ 次读数精确恢复 $q_{k+1}(x)$。

证明。在 $0\le n\le P-1$ 内，$0\le r+n\le2P-2$，最多向第 $k$ 位携带一次，且
$$
d_k(x+n)=\left(b+\left\lfloor\frac{r+n}{P}\right\rfloor\right)\bmod p.
\tag{24.105}
$$
$r=0$ 时商始终零；$r>0$ 时首次商一恰在 $\tau=P-r\in\{1,\ldots,P-1\}$。$p\ge2$ 保证 $b$ 与 $(b+1)\bmod p$ 不同，包括 $b=p-1$ 到零的环绕。故变化时刻恢复低位余数。反向，所有加一后的高位都通过 $q_{k+1}$ 因子化，得到核等式。$k=0$ 时 $P=1$、只读一次，变化时刻集为空，$r$ 只能为零，恰为 $d_0=q_1$。$\square$

**定理 24.9（固定连续协议的锐最坏时域）。** 对 $k\ge1$，若 $0\le N<P-1$，则 $W_{k,N}$ 不能在全部初态上恢复 $q_{k+1}$。该协议的必要且充分最大时域为 $P-1$，读数数为 $P$。

证明。取整数初态 $x=0,x'=1$，高位均为零、低位余数分别零和一。$0\le n\le N\le P-2$ 时，$n,n+1\in[0,P-1]$，所以两个高位读数都为零，但 $q_{k+1}(0)\ne q_{k+1}(1)$。在 $n=P-1$ 后一条首次变一，前一条仍零。充分性由定理24.8给出。

该下界仅针对规定的从零开始连续全采样协议，不比较自适应、跳跃采样、二分搜索、变更端口或直接读取 $q_{k+1}$；这些协议另需时刻可达、回溯、复制及费用合同。等待时域和实际读取次数是不同费用坐标。$\square$

**推论 24.10（单高位的最小动态稳定细化）。** 对唯一合法动作 $T$ 和传感器 $d_k$，
$$
\bigl[\forall n\ge0,\ d_k(T^nx)=d_k(T^ny)\bigr]
\iff q_{k+1}(x)=q_{k+1}(y).
$$
最小保留 $d_k$ 且在 $T$ 下闭合的实际行为表示就是 $q_{k+1}$，有 $p^{k+1}$ 个行为类。

证明。定理24.8给从全部历史相等到模态相等，模 $p^{k+1}$ 的加一闭合给反向。若表示 $r_*$ 恢复 $d_k$ 且满足 $r_*T=\overline T r_*$，归纳使相同表示给全部未来高位相同，继而给相同 $q_{k+1}$。后者本身恢复 $d_k$ 且满足 $q_{k+1}(Tx)=q_{k+1}(x)+1$。直接应用本卷第2—3节及 `DynamicClosureMinimality.dynamic_closure_is_least` 的一般最小因子化结论即可。

更长历史不能区分 $x$ 与 $x+p^{k+1}$。当前只有 $p$ 值的高位接口，经最多 $p^k-1$ 步可恢复 $p^{k+1}$ 个行为类；也可由较宽的当前 $q_{k+1}$ 直接承载它们。事件数始终保留，恢复初始模态后可算当前模态。与命题24.4对照，已经闭合的 $q_k$ 等待不增加区别，未闭合的 $d_k$ 则通过携带取得遗漏低位；两者都不能继续取得未耦合到接口的更高位。$\square$

**命题 24.11（有限角色、事件频率与其核）。** 对 $m\ge0$、$j\in\mathbb Z/p^m\mathbb Z$，定义
$$
\chi_{m,j}(x)=\exp\left(\frac{2\pi i j[q_m(x)]}{p^m}\right).
$$
它是连续加法角色，满足
$$
\chi_{m,j}(Tx)=e^{2\pi i j/p^m}\chi_{m,j}(x).
\tag{24.106}
$$
其最小正事件周期为 $p^m/\gcd(j,p^m)$，$j=0$ 时取一。$m\ge1$ 时，与 $p$ 互素的 $j$ 恰具有 $q_m$ 的完整分辨率；$m=0$ 为唯一平凡角色。

证明。更换整数代表只改变指数中 $2\pi i$ 的整数倍，加法公式给同态性。它通过连续有限离散商 $q_m$ 因子化，故连续；代入 $x+1$ 给式（24.106）。正周期 $h$ 恰满足 $p^m\mid jh$，同命题24.3的除法得到最小值。两个初态在全部该角色历史下相同，恰当
$$
j(q_m(x)-q_m(y))=0\pmod {p^m}.
$$
$j$ 与 $p$ 互素时可消去；不互素时有非零模差被其消去。特别 $j=1$ 的 $p^m$ 个相位值互异。此处频率单位是每次加一，角频率按 $2\pi$ 取模；有限精确相位的访问仍须协议许可。标准紧群平移与角色背景参见 Walters, *An Introduction to Ergodic Theory*, Springer, 1982。这里仅定义 p 幂子族，不声称已证明全部 $\mathbb Z_p$ 连续角色的分类，也不把全模 profinite 分类未经映射直接移来。$\square$

**命题 24.12（完整相容读数与有限球）。** 任意相容序列 $a_m\in\mathbb Z/p^m\mathbb Z$，满足 $a_{m+1}\bmod p^m=a_m$，由唯一 $x\in\mathbb Z_p$ 实现。有限前缀 $a_0,\ldots,a_K$ 的实现则恰为 $a+p^K\mathbb Z_p$，其中 $a$ 是 $a_K$ 的整数提升。

证明。取规范整数代表 $r_m=[a_m]$；$m\ge n$ 时 $p^n\mid r_m-r_n$，故 $(r_m)$ 为 p 进 Cauchy 序列。完备性给极限 $x$，各 $q_n$ 连续且纤维闭，尾部 $q_n(r_m)=a_n$，所以 $q_n(x)=a_n$。若 $x,y$ 全部投影相同，$|x-y|_p\le p^{-n}$ 对每个 $n$ 成立，故 $x=y$。有限前缀由最高精度同余给出。无界深度的相容子序列也决定全部层：对每层选任意更细读数约化，相容性使选择无关。

每个有限前缀可有非负整数代表，完整极限未必非负整数，例如 $a_m=p^m-1$ 实现 $x=-1$，其非负代表作为实数发散。甚至完整极限未必属于任何普通整数：令 $a_m$ 是 $1+p$ 在模 $p^m$ 下的乘法逆，唯一性保证这些值相容，其极限为 $(1+p)^{-1}\in\mathbb Z_p$，而没有整数 $z$ 满足 $(1+p)z=1$。完成域的实现不等于原载体的实现；相容完成也不生成下一位或分配概率。$\square$

**命题 24.13（确定轨道的有限访问计数）。** 对固定 $x,m$ 和模 $p^m$ 的目标值，每 $p^m$ 个连续时刻恰访问一次。前 $N\ge1$ 个时刻的访问数为 $\lfloor N/p^m\rfloor$ 或 $\lceil N/p^m\rceil$，频率与 $p^{-m}$ 之差至多 $1/N$。

证明。$q_m(x+n)$ 在每个完整块遍历有限循环一次，除法算法把 $N$ 拆成完整块及一个不完整块，后者对每个值至多增加一次。此比例不需要概率律，也不同于命题24.11的相位频率；若实际停留长度依状态改变，按钟时的比例还需运输相应权重，本命题只计已知等步事件。$\square$

**假设 24.14（额外指定 Haar 初态律）。** 另在紧加法群 $\mathbb Z_p$ 上指定归一化平移不变 Haar 概率 $\mu$，令 $X\sim\mu$。一般紧群 Haar 定理提供该律，亦可用独立均匀 p 进数字构造；完成化与加一动作自身不指定此律。下项仅对有限商和有限记录计算自然对数 Shannon 熵，不给整个无穷精度状态定义有限离散熵。

**命题 24.15（同源历史熵与确定性显露）。** 在假设24.14下，
$$
\mu(a+p^m\mathbb Z_p)=p^{-m},\quad
H(q_m(X))=m\log p,\quad
H(q_{m+1}(X)\mid q_m(X))=\log p.
\tag{24.107}
$$
固定低模的任何包含至少一次已知时刻读数的有限历史熵为 $m\log p$，其后新增同精度读数条件熵为零；而
$$
H(W_{k,p^k-1}(X))=(k+1)\log p,\qquad
H(W_{k,p^k-1}(X)\mid d_k(X))=k\log p.
\tag{24.108}
$$
证明。$p^m$ 个剩余类被平移互换且分割全空间，所以各质量为 $p^{-m}$。等概率有限集合的熵即 $m\log p$；每个旧球的 $p$ 个更细球各占条件质量 $1/p$，给条件熵。命题24.4使低模历史与 $q_m$ 的实际像双射，后续读数由它确定。定理24.8使指定高位历史与 $q_{k+1}$ 的实际像双射，故联合熵为 $(k+1)\log p$；$d_k$ 均匀于 $p$ 个值且是该历史的分量，条件熵为相减所得 $k\log p$。

这些读数高度相关，不能把 $p^k$ 份单次熵直接相加。增长来自同一初态的低位被显露，动作没有增加随机创新；$T$ 保持 $\mu$ 且可逆等距，不由记录熵增长推出热力学熵增或物理反演破缺。若另有旧记录，应在保留的同一联合律下条件化；非 Haar 初态的球概率不同，Dirac 初态更使全部记录熵为零。有限加一与携带恢复的算术对任意整数基 $b\ge2$ 同样成立，故层级周期本身不能识别素数；标准 $\mathbb Z_p$ 赋值和距离才使用素数假设。传感器误码或动作漏记不在定义24.1内，需另立共同误差纤维，不能继续声称这里的锐阈值。$\square$

## 24.99 追加锚

## 25. 非线性双端口、共同钟与档案相容图

**定义 25.1（实际混合响应合同）。** 固定已知 $\nu>0$、紧区间 $I=[b_-,b_+]$（允许单点）和 $T_0>0$，记 $B=\max\{|b_-|,|b_+|\}$。同一来源、模型、校准和内部时间下有实际实值响应 $r(\beta,t),z(\beta,t)$，定义在 $I$ 的开邻域乘 $[0,T_0]$ 上，满足
$$
r(\beta,0)=z(\beta,0)=0,\quad r_t(\beta,0)=\nu,
\quad z_t(\beta,0)=\beta.
\tag{25.101}
$$
假设时间二阶导数及其一次 $\beta$ 导数连续，所需低阶导数亦连续，时间端点取单侧导数；在 $I\times[0,T_0]$ 有非负有限常数
$$
|r_{tt}|\le A_r,\quad |r_{\beta tt}|\le A_1,
\qquad |z_{tt}|\le C_z,\quad |z_{\beta tt}|\le C_1.
\tag{25.102}
$$
这些是实际响应的估计前提，不是参数单射性前提。置
$$
\kappa=C_1/2+A_1(B+C_zT_0)/\nu,
\quad 0<T\le T_0,\quad A_rT\le\nu/2,\quad\kappa T\le1/2,
$$
$$
s_*=\nu T/2,\qquad L_g=2(B+C_zT)/\nu.
\tag{25.103}
$$
零系数不限制 $T$，所以这样的正 $T$ 存在。这里 $A_r$ 是进度响应常数，与准备幅度上界 $A_\alpha$ 无关。

**定理 25.2（阈值图、精确像与共同短时单射）。** 在定义25.1下，每个 $\beta\in I$、$s\in[0,s_*]$ 有唯一 $t_\beta(s)\in[0,T]$ 使 $r(\beta,t_\beta(s))=s$。设 $G_s(\beta)=z(\beta,t_\beta(s))$，则正阈值处
$$
\frac{2s}{3\nu}\le t_\beta(s)\le\frac{2s}\nu,
\qquad \partial_s t_\beta=\frac1{r_t},\quad
\partial_\beta t_\beta=-\frac{r_\beta}{r_t},
\tag{25.104}
$$
$$
\partial_\beta G_s=z_\beta-z_t\frac{r_\beta}{r_t},
\quad \frac{s}{3\nu}\le\partial_\beta G_s\le\frac{3s}{\nu},
\quad
\left|\partial_\beta G_s-\frac{s}{\nu}\right|
\le\frac4{\nu^2}\left(\kappa+\frac{A_r}{2\nu}\right)s^2.
\tag{25.105}
$$
实际映射 $\Psi(\beta,t)=(r(\beta,t),z(\beta,t))$ 在
$$
W=\{(\beta,t):\beta\in I,\ 0<t\le T,\ 0<r(\beta,t)\le s_*\}
\tag{25.106}
$$
上单射，其精确像为
$$
Y=\{(s,w):0<s\le s_*,\quad G_s(b_-)\le w\le G_s(b_+)\}.
\tag{25.107}
$$
域含 $I\times(0,T/3]$。按坐标次序 $(t,\beta)$，Jacobian 行列式满足
$$
\Delta=r_tz_\beta-r_\beta z_t\ge\nu t/4>0.
\tag{25.108}
$$

证明。Taylor 积分式及其参数微分给
$$
\begin{aligned}
|r-\nu t|&\le A_rt^2/2,& |r_t-\nu|&\le A_rt,& |r_\beta|&\le A_1t^2/2,\\
|z-\beta t|&\le C_zt^2/2,& |z_t-\beta|&\le C_zt,& |z_\beta-t|&\le C_1t^2/2.
\end{aligned}
\tag{25.109}
$$
例如 $r-\nu t=\int_0^t(t-v)r_{tt}(\beta,v)dv$；混合导数连续使在此积分下对 $\beta$ 求导合法，其余五式同理。因此 $\nu/2\le r_t\le3\nu/2$，积分得 $(\nu/2)t\le r\le(3\nu/2)t$。更精细地 $r(\beta,T)\ge3\nu T/4>s_*$，故介值性及严格时间单调性给唯一阈值时刻，且正阈值严格在 $T$ 之前。隐函数定理在这些内部时间点适用；参数开邻域保证区间端点的导数也是限制所得。$s=0$ 时 $t_\beta(0)=0$，公式按单侧连续意义延伸。

链式法则必须保留参数依赖的阈值时间，给（25.105）的首式。记 $t=t_\beta(s)$，有
$$
|\partial_\beta G_s-t|
\le\left(C_1/2+A_1(B+C_zT)/\nu\right)t^2
\le\kappa t^2\le t/2.
$$
结合（25.104）的时间界即得两侧导数界；再用 $|t-s/\nu|\le A_rt^2/(2\nu)$ 得二阶渐近界。因此每条正阈值图对参数严格递增。两份相等读数先落在同一正阈值，再由严格递增得同一参数，最后由 $r$ 的时间单调性得同一时间。连续严格单调函数的像是端点间闭区间，给（25.107）；单点参数时该像退化成一条曲线。$t\le T/3$ 保证 $r\le s_*$。最后 $\Delta=r_t\partial_\beta G_s\ge(\nu/2)(t/2)$。此证明没有把 $r$ 假定成与参数无关，也没有将 $t=s/\nu$ 或 $\beta=\nu w/s$ 当作精确反演式。$\square$

**定理 25.3（两份实际读数的参数与时间误差）。** 对 $(s,w)=\Psi(\beta,t)$、$(s',w')=\Psi(\beta',t')\in Y$，置 $m=\min\{s,s'\}>0$。则
$$
|\beta-\beta'|\le\frac{3\nu}{m}\bigl(|w-w'|+L_g|s-s'|\bigr),
\tag{25.110}
$$
$$
|t-t'|\le\frac2\nu|s-s'|+
 \frac{4A_1m^2}{\nu^3}|\beta-\beta'|,
\tag{25.111}
$$
因而
$$
|t-t'|\le\left(\frac2\nu+\frac{12A_1L_gm}{\nu^2}\right)|s-s'|
 +\frac{12A_1m}{\nu^2}|w-w'|.
\tag{25.112}
$$
若同一测得坐标的真实点和拟合点均在 $s\ge s_0>0$ 的图中，且各有坐标残差至多 $\epsilon_r,\epsilon_z$，则参数差至多 $6\nu(\epsilon_z+L_g\epsilon_r)/s_0$。

证明。由（25.104）和（25.109），$|\partial_sG_s|=|z_t/r_t|\le L_g$。不妨 $s=m\le s'$，则在同一阈值 $m$ 比较两个参数，得到
$$
\frac{m}{3\nu}|\beta-\beta'|
\le|G_m(\beta)-G_m(\beta')|
\le |w-w'|+L_g(s'-m).
$$
这给（25.110）。阈值时间的导数满足 $|\partial_st|\le2/\nu$，在 $m$ 处 $|\partial_\beta t_\beta(m)|\le A_1t_\beta(m)^2/\nu\le4A_1m^2/\nu^3$；同样先同阈值比参数再移动阈值给（25.111），代入得（25.112）。噪声结论用两个候选之间的坐标差各至多两倍残差界。测得坐标本身无需在 $Y$ 中。

正阈值下截断图的逆统一 Lipschitz；靠近零时参数界的 $1/m$ 因子不能仅凭时间界删掉。例如合法响应 $r=\nu t,z=\beta t$ 在固定 $t$ 给 $|\delta z|=t|\delta\beta|$，已排除延伸到零的统一参数 Lipschitz 常数。$\square$

**约定 25.4（同轨迹同时取得与未知钟）。** 双端口实际取得须同时、不扰动，或有已认证的等价共同轨迹，使两数确实等于同一 $\Psi(\beta,t)$。仅有“两个仪器同时开机”不足以证明测量干预没有改变方程。固定同一个严格递增连续钟 $t=h(\theta)$、$h(0)=0$。如果实际 $(\beta,h(\theta))\in W$，同时读数经上述逆确定参数和该样点的内部时间，无需钟导数。有限多个样点只确定相应 $h(\theta_i)$，不确定未采样插值。校准、黏性、模型和已知准备幅度必须在所有候选间固定。

阈值 $s$ 是已读第一坐标，不额外算一次导数测量。若实际采用首次阈值触发，则另须有事件检测权限、第一分支保证，以及 $h(\theta_{\rm end})\ge t_\beta(s)$ 的可达性；$h(\theta_{\rm end})\ge2s/\nu$ 或 $\ge T$ 是充分条件。连续性给到达，初始分支严格单调性给唯一首次交叉。仅严格增的钟 $h(\theta)=c(1-e^{-\theta})$ 在 $0<c<t_\beta(s)$ 时永远不到阈值。任意迟时样点的 $r$ 数值小也不证明它在初始分支；预定外部时刻需独立的内部时间上界或分支证书。

**定义 25.5（完整观察者与共同实现交集）。** 完整观察者明确写为
$$
H=(C,\mathcal A,d_{\rm raw}).
\tag{25.113}
$$
$C$ 包含所有已取得的内部／外部旧记录及其关系；$\mathcal A$ 是带来源索引的合法取得历史，保留每次动作、端口、外部标签、校准及共同轨迹证书；$d_{\rm raw}$ 是当前实际原始对，不能由预测值代写。

固定模型和校准后，令 $\Omega$ 为完整实现集合。每个 $\omega\in\Omega$ 同时包含一个来源身份、参数 $\beta(\omega)$、同一准备生成的整条实际轨迹、一个共同钟 $h_\omega$，以及解释全部旧记录所需的辅助变量、误差和关系。每条旧记录 $c_i\in C$ 有其声明的约束 $\mathcal R_i(\omega,c_i)$；关系可包括跨端口、跨时刻和跨来源的已获信息，不能逐条另选实现。令 $\operatorname{Hist}(\omega,\mathcal A)$ 断言该一份实现确实支持所记合法取得及同时无扰动／等价轨迹条件。当前外部时刻 $\theta_*$ 的内部时刻为 $t(\omega)=h_\omega(\theta_*)$。将原始对按固定校准换为 $(r_{\rm obs},z_{\rm obs})$，其共同误差事件记为 $\mathcal E_H$。定义
$$
\begin{aligned}
\mathfrak F_H=\{\omega\in\Omega:\;&\operatorname{Hist}(\omega,\mathcal A),\quad
 \mathcal R_i(\omega,c_i)\ \text{对全部旧记录成立},\\
 & (\beta(\omega),t(\omega))\in W,\quad \omega\in\mathcal E_H,\\
 &|r(\beta(\omega),t(\omega))-r_{\rm obs}|\le\epsilon_r,\\
 &|z(\beta(\omega),t(\omega))-z_{\rm obs}|\le\epsilon_z\},
\end{aligned}
\tag{25.114}
$$
并令 $K_H=\{(\beta(\omega),t(\omega)):\omega\in\mathfrak F_H\}$。如果原始实际误差为 $|x_{\rm obs}-x|\le\epsilon_x$、$|y_{\rm obs}-y|\le\epsilon_y$，且 $r=1-2x/\alpha,z=-4y/\alpha$，则在同一个联合误差事件上使用
$$
\epsilon_r=2\epsilon_x/|\alpha|,\qquad
\epsilon_z=4\epsilon_y/|\alpha|.
\tag{25.115}
$$
此处 $\alpha$ 已知固定，不将含噪幅度代入当作新的联合识别证明。$\mathcal E_H$ 可以施加更强的相关误差约束，无独立噪声前提。

**命题 25.6（外包界可限制，档案见证不可省略）。** 令
$$
K_{\rm pair}=\{(\beta,t)\in W:
 |r(\beta,t)-r_{\rm obs}|\le\epsilon_r,
 |z(\beta,t)-z_{\rm obs}|\le\epsilon_z\}.
\tag{25.116}
$$
则 $K_H\subseteq K_{\rm pair}$。定理25.3对任意两个外包候选的直径上界也对 $K_H$ 成立；第27节的共同剩余时域界亦如此。但是声称拟合点与完整档案相容，必须给 $\widehat\omega\in\mathfrak F_H$，不能只给 $(\widehat\beta,\widehat t)\in K_{\rm pair}$。

证明。集合包含由（25.114）投影直接得到；全称成对不等式可限制到子集。反方向失败：某条旧约束可能要求 $\beta=b_-$，而当前精确对只由另一个参数生成，外包非空而交集空。全部旧记录分别可拟合也不推出一个共同 $\omega$ 存在。若实际来源、档案、第一分支和联合误差假设均成立，真实 $\omega$ 就给非空见证；否则不能以空集上的真空全称断言授权动作。完整 $H$ 的保留还意味着从两数恢复场并不等于从两数重建整份档案。$\square$

## 26. 全 PDE 的参数差商与联合识别实例

**定理 26.1（开邻域上的实际参数导数）。** 固定已知 $\nu>0$、$0<a\le|\alpha|\le A_\alpha$ 及 $B_0\ge0$，使用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义25.1的全部空间、归一化、准备和常数 $R,\tau$。令 $X=C([0,\tau];H^2_\sigma)$、$\lambda=1/(4R)$、$\delta_\beta=R/24$。同一实际温和解可定义在参数开区间
$$
J_\beta=(-B_0-\delta_\beta,B_0+\delta_\beta),
\tag{26.101}
$$
且 $\beta\mapsto u_\beta\in X$ 为 $C^1$，满足
$$
\|\partial_\beta u_\beta\|_X\le6.
\tag{26.102}
$$

证明。只使用恢复卷定理25.3的同一双线性算子 $\mathcal B$，不重新构造 PDE。将 $\beta$ 投影到 $[-B_0,B_0]$，初态范数增加至多 $3\delta_\beta=R/8$，故开区间初态范数小于或等于 $5R/8$。同一 $R$ 球上的映射像范数至多 $5R/8+R/4=7R/8$，收缩系数仍为 $1/2$。因此同一时间与同一球适用，且相减仍给 $\|u_\beta-u_\gamma\|_X\le6|\beta-\gamma|$。

定义有界线性算子 $\mathcal A_\beta v=\mathcal B(v,u_\beta)+\mathcal B(u_\beta,v)$，其范数至多 $2\lambda R=1/2$。Neumann 级数给 $(I+\mathcal A_\beta)^{-1}$，范数至多二。令
$$
v_\beta=(I+\mathcal A_\beta)^{-1}E(\cdot)b_0,
\quad
v_\beta=E(\cdot)b_0-\mathcal B(v_\beta,u_\beta)-\mathcal B(u_\beta,v_\beta).
\tag{26.103}
$$
$\|b_0\|_{H^2}=3$ 给 $\|v_\beta\|_X\le6$。对 $h\ne0$ 且 $\beta+h\in J_\beta$，实际差商 $q_h=(u_{\beta+h}-u_\beta)/h$ 满足 $\|q_h\|_X\le6$。将两个二次温和方程精确相减得
$$
(I+\mathcal A_\beta)q_h=E(\cdot)b_0-h\mathcal B(q_h,q_h),
\quad
\|q_h-v_\beta\|_X\le72\lambda|h|.
\tag{26.104}
$$
这证明真实参数导数存在于整个时间 Banach 空间，而不是假定逐点可微。再将（26.103）在两参数处相减，得到
$$
\|v_\beta-v_\gamma\|_X
\le2\|\mathcal A_\beta-\mathcal A_\gamma\|\,\|v_\gamma\|_X
\le24\lambda\|u_\beta-u_\gamma\|_X
\le144\lambda|\beta-\gamma|.
\tag{26.105}
$$
故导数连续；原闭区间端点的导数来自这个真正的开邻域。$\square$

**定理 26.2（$DF$、$DG$ 与连续混合端口界）。** 继续使用恢复卷的 $F:H^2_\sigma\to L^2_\sigma$、$Q_\phi$、$G_\phi$、$M_F,D_F,J,M$。对其任一配对端口 $(\ell,\phi)$，
$$
DF(u)h=\nu\Delta h-\mathbb P((h\cdot\nabla)u+(u\cdot\nabla)h),
$$
$$
DG_\phi(u)h=-\nu\ell(DF(u)h)
 -D^2Q_\phi(h,F(u))-DQ_\phi(u)DF(u)h.
\tag{26.106}
$$
这些是连续 Fréchet 导数；在半径 $R$ 球中
$$
\|DF(u)h\|_2\le D_F\|h\|_{H^2},\qquad
|DG_\phi(u)h|\le J\|h\|_{H^2}.
\tag{26.107}
$$
实际两个端口满足
$$
|x_{tt}|,|y_{tt}|\le M,\qquad
|\partial_\beta x_{tt}|,|\partial_\beta y_{tt}|\le6J,
\tag{26.108}
$$
这些混合导数在参数与时间上连续，包含时间零点的单侧值。

证明。恢复卷的 $\|u\|_\infty\le4\|u\|_{H^2}$ 使对流为连续双线性映射 $H^2\times H^2\to L^2$。二次展开余项至多 $4\|h\|_{H^2}^2$，故 $DF$ 的公式与连续性确实成立，范数界为 $\nu+8R$。恢复卷引理25.5已在完整 $L^2$ 空间证明 $Q_\phi,DQ_\phi,D^2Q_\phi$ 及其界；此处对 $G_\phi=-\nu\ell F-DQ_\phi(\cdot)F$ 用乘积法则，给（26.106）。三项界之和为
$$
\nu D_F+M_F+RD_F=\nu^2+10\nu R+12R^2=J.
$$
$G_\phi$ 是 $H^2$ 上连续线性、双线性、三线性映射之和。将这些映射逐时作用于 $C_tH^2$，仍为连续多线性映射，因而诱导映射 $C_tH^2\to C_t\mathbb R$ 为 $C^1$，导数逐时为 $DG_\phi$。定理26.1于是给
$$
\partial_\beta a_{tt}(\beta,t)=DG_\phi(u_\beta(t))v_\beta(t),
$$
范数至多 $6J$，且联合连续。绝对二阶界是恢复卷定理25.6的 $M$。最后由
$$
a(\beta,t)=a(\beta,0)+t a_t(\beta,0)
 +\int_0^t(t-s)G_\phi(u_\beta(s))\,ds
\tag{26.109}
$$
在连续时间函数空间对参数求导，其结果可再对时间微分两次，正好得到上式。因此没有把未证的混合导数交换作为前提，也没有要求 $u_{tt}\in L^2$ 或 $u_t\in H^2$。$\square$

**推论 26.3（已校准 PDE 的双端口绝对钟图）。** 对恢复卷（25.115）的实际端口置
$$
r=1-2x/\alpha,\qquad z=-4y/\alpha,\qquad
A_r=2M/a,\quad C_z=4M/a,\quad A_1=12J/a,\quad C_1=24J/a.
\tag{26.110}
$$
取 $I=[-B_0,B_0]$、$T_0=\tau$，并取
$$
\kappa=C_1/2+A_1(B_0+C_z\tau)/\nu,
\quad T=\min\{\tau,\nu/(2A_r),1/(2\kappa)\},\quad s_*=\nu T/2.
\tag{26.111}
$$
则定义25.1的全部条件实际成立，定理25.2、25.3的图、精确像、单射性及全部误差界适用于这个全 PDE。这里 $A_r,\kappa$ 严格正，故公式无零分母。

证明。恢复卷的初始系数识别给 $x(0)=\alpha/2$、$y(0)=0$、$y_t(0)=-\alpha\beta/4$。没有两个非零初始频率相加为 $(1,0)$，所以该处非线性导数为零，$x_t(0)=-\nu\alpha/2$。由真实 $u_t=F(u)$ 得 $r_t(0)=\nu,z_t(0)=\beta$，并非有限槽的代数代替了演化。定理26.2乘固定比例并用 $|\alpha|\ge a$ 给（26.110），定理26.1供应开邻域。时间选择满足（25.103），直接使用已证一般图定理即可。

在同轨迹同时读出及第一分支条件下，一对正时原始数据确定 $\beta$ 和该样点内部时间；多个样点仍只给采样处的钟值。带噪应用须用定义25.5的一份实现与联合事件，尤其原始误差转换严格为（25.115）。本结论固定 $\alpha,\nu$、模型及校准；恢复卷的含噪 $\alpha$ 标量估计不将这些固定量变成未知量。

若 $B_0>0$，不同初态在时间零的规范读数全为 $(0,0)$，所以不能将它加入原始图并保留单射性。若 $B_0=0$，初态已知且参数域单点，$r_t\ge\nu/2$ 使加入时间零仍单射；正阈值的参数除法界仍只在其原声明域内使用。$\square$

**命题 26.4（未知黏性的精确钟碰撞与条件性纤维）。** 在 $\beta=0$ 的实际 PDE 中，
$$
u(X,t)=\alpha e^{-\nu t}(0,\cos X_1),\quad p=0,
\quad r=1-e^{-\nu t},\quad z=0.
\tag{26.112}
$$
两种正黏性及满足 $\nu_1h_1=\nu_2h_2$ 的钟给相同的整个双端口历史，故未知黏性下不能在包含此准备的族上由这些历史恢复绝对内部时间。该例不证明隐藏参数不同，因为两例都取 $\beta=0$。

证明。该剪切的对流为零、Laplacian 为负自身，所以方程逐项成立；读出与钟等式直接代入即得。一般混合合同本身也不能识别三个量：精确响应 $r=\nu t,z=\beta t$ 在 $(\nu,\beta,t)\mapsto(c\nu,c\beta,t/c)$ 下不变。后者只是合同反例，不是固定 $\alpha$ 的非线性 PDE 缩放定律。

另有如下严格条件命题：若额外证明实际响应在正黏性开邻域对 $(\nu,\beta,t)$ 为 $C^1$，且在所考察内点有统一渐近
$$
r_\nu=t+O(t^2),\quad z_\nu=O(t^2),\quad
r_t=\nu+O(t),\quad z_t=\beta+O(t),\quad
r_\beta=O(t^2),\quad z_\beta=t+O(t^2),
\tag{26.113}
$$
则固定一对足够短正时读数时，隐函数定理给随 $\nu$ 改变的精确局部纤维 $(\beta(\nu),t(\nu))$，且
$$
\frac{dt}{d\nu}=\frac{r_\beta z_\nu-z_\beta r_\nu}{\Delta}
=-\frac t\nu+O(t^2),\quad
\frac{d\beta}{d\nu}=\frac{z_t r_\nu-r_tz_\nu}{\Delta}
=\frac\beta\nu+O(t).
\tag{26.114}
$$
证明这个条件命题只需定理25.2的非零 Jacobian：对固定读数求导解二乘二线性方程，代入（26.113）及 $\Delta=\nu t+O(t^2)$ 即得。在非零内点 $\beta$ 处，充分小时间使两导数非零。定理26.1仅证明固定黏性下的 $\beta$ 可微性，没有证明（26.113）的黏性前提，所以这里保持条件命题；不将它升级为本节已履行的 PDE 黏性识别或不识别结论。更多端口或整条非退化响应曲线需要另行研究。$\square$

## 27. 比值边界、完整场因子与部分续接

**定理 27.1（隐藏初始方向的正则比值坐标）。** 固定推论26.3的全部准备、黏性、常数和第一分支。置
$$
\vartheta(\beta,t)=\nu z(\beta,t)/r(\beta,t)\quad(t>0),
\qquad \vartheta(\beta,0)=\beta,
$$
$$
Z_*=B_0+C_zT/2,\quad E_\vartheta=C_z+A_rB_0/\nu,
\quad L_\vartheta=C_z+2A_rZ_*/\nu,
\quad D_\vartheta=C_1+A_r/\nu+2A_1Z_*/\nu.
\tag{27.101}
$$
则 $\vartheta$ 是 $[-B_0,B_0]\times[0,T]$ 上的 $C^1$ 函数（时间端点单侧），并有
$$
|\vartheta-\beta|\le E_\vartheta t,\quad
|\vartheta_t|\le L_\vartheta,\quad
|\vartheta_\beta-1|\le D_\vartheta t,
\quad 1/3\le\vartheta_\beta\le3.
\tag{27.102}
$$
初始边界导数为
$$
\vartheta_\beta(\beta,0)=1,\qquad
\vartheta_t(\beta,0)=\tfrac12 z_{tt}(\beta,0)
 -\frac{\beta}{2\nu}r_{tt}(\beta,0).
\tag{27.103}
$$

证明。先分离已知的一阶时间零点，定义
$$
U(\beta,t)=\int_0^1r_t(\beta,qt)\,dq,
\quad V(\beta,t)=\int_0^1z_t(\beta,qt)\,dq.
\tag{27.104}
$$
于是 $r=tU,z=tV$，$U(\beta,0)=\nu,V(\beta,0)=\beta$。第26节的连续混合正则性保证 $U,V$ 均 $C^1$，且由（25.109）积分得到
$$
\begin{gathered}
U\ge\nu/2,\quad |U-\nu|\le A_rt/2,\quad
|V-\beta|\le C_zt/2,\quad |V|\le Z_*,\\
|U_t|\le A_r/2,\quad |V_t|\le C_z/2,\quad
|U_\beta|\le A_1t/2,\quad |V_\beta-1|\le C_1t/2.
\end{gathered}
\tag{27.105}
$$
因此 $\nu V/U$ 就是在零点也有定义的 $C^1$ 延伸。由 $\nu V-\beta U=\nu(V-\beta)+\beta(\nu-U)$ 得第一误差界；对商求时间导数，用（27.105）给 $C_z+2A_rZ_*/\nu$。参数导数减一，分别界定 $\nu(V_\beta-1)/U$、$\nu/U-1$ 及 $\nu VU_\beta/U^2$，得到 $D_\vartheta t$。代入零点的积分导数给（27.103）。

正的参数导数不需再缩短 $T$。对 $t>0$，
$$
\vartheta_\beta=\frac\nu r\left(z_\beta-\frac zr r_\beta\right),\qquad
\left|z_\beta-\frac zr r_\beta-t\right|
\le\left(C_1/2+A_1Z_*/\nu\right)t^2
\le\kappa t^2\le t/2.
$$
再用 $(\nu/2)t\le r\le(3\nu/2)t$ 得 $1/3\le\vartheta_\beta\le3$，零点由（27.103）直接成立。$\square$

**定理 27.2（闭合提升图及两种完成）。** 令
$$
\overline W=\{(\beta,t):|\beta|\le B_0,\ 0\le t\le T,
\ r(\beta,t)\le s_*\},\quad
\widetilde\Psi(\beta,t)=(r(\beta,t),\vartheta(\beta,t)).
\tag{27.106}
$$
该图在闭域上单射，且为双 Lipschitz 坐标。置 $\Theta_s(\beta)=\vartheta(\beta,t_\beta(s))$，包括 $\Theta_0(\beta)=\beta$，$L_s=2L_\vartheta/\nu$。其精确像是闭带
$$
\widetilde Y=\{(s,v):0\le s\le s_*,\quad
\Theta_s(-B_0)\le v\le\Theta_s(B_0)\},
\tag{27.107}
$$
且任意两份提升图读数 $(s,v),(s',v')$、$m=\min\{s,s'\}\ge0$ 满足
$$
|\beta-\beta'|\le3(|v-v'|+L_s|s-s'|),
\qquad
|t-t'|\le\frac2\nu|s-s'|+
 \frac{4A_1m^2}{\nu^3}|\beta-\beta'|.
\tag{27.108}
$$
当 $B_0>0$ 时，原始正时间图 $Y$ 的 Euclidean 完成只在初始边界加一个点 $(0,0)$，提升图正时间部分的 Euclidean 完成却加整段 $\{0\}\times[-B_0,B_0]$。两种误差几何在该边界附近不统一等价。

证明。正 $s$ 处，$\Theta_s=(\nu/s)G_s$，所以（25.105）给 $1/3\le\partial_\beta\Theta_s\le3$；零点的导数为一。$|\partial_s\Theta_s|=|\vartheta_t/r_t|\le L_s$。正时间的单射性复用定理25.2；$s=0$ 强制 $t=0$，第二坐标恰是参数。连续单调阈值图给闭带像。两参数先在较小阈值 $m$ 比较，再沿阈值移动，得（27.108）；$m=0$ 时阈值时间恒为零，所以其参数变化项就是零，毋须除零或极限论证。前向估计为
$$
|s-s'|\le\tfrac12A_1T^2|\beta-\beta'|+\tfrac32\nu|t-t'|,
\quad
|v-v'|\le3|\beta-\beta'|+L_\vartheta|t-t'|.
\tag{27.109}
$$
这是沿环境参数／时间矩形的两段比较，故不要求连接线留在 $\overline W$。逆估计中的 $m\le s_*$ 给统一常数，证明双 Lipschitz 性。

正时 Jacobian 为
$$
r_t\vartheta_\beta-r_\beta\vartheta_t
=\frac\nu r\Delta\ge\nu/6,
\tag{27.110}
$$
零时为 $\nu$。若需普通开集上的局部逆，可以在负时间附近定义 $U=\nu+t r_{tt}(\beta,0)/2$、$V=\beta+t z_{tt}(\beta,0)/2$。第26节混合导数使这些初始系数对参数 $C^1$，两侧的一阶值吻合，给 $C^1$ 延伸及非零 Jacobian。正阈值端点严格小于 $T$，参数端点有开邻域，故局部逆在所有相关边界均以限制意义成立。此代数延伸不声称负时间 PDE 演化存在。

原始图精确分解为
$$
(\beta,t)\longmapsto(s,\vartheta)
\longmapsto(s,s\vartheta/\nu)=(r,z).
\tag{27.111}
$$
闭参数／阈值域紧，两个完整像均为紧集，其正阈值部分稠密，故各自闭像就是各自 Euclidean 完成。第二映射在 $s=0$ 将整段压为一点。选不同的 $\beta,\beta'$，$s_n=s_*/(n+1)\downarrow0$，两原始序列 $(s_n,G_{s_n}(\beta))$、$(s_n,G_{s_n}(\beta'))$ 均趋 $(0,0)$，但提升序列分别趋 $(0,\beta)$、$(0,\beta')$。所以原始到提升的正时间变换不统一连续。普通原始度量的完成不能凭空恢复这些标签。

已有 [GoldenThreadBlowup](../../../D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.lean) 的 `golden_thread_completion_value_eq`、`golden_thread_tangent_injective` 与 `golden_geometric_thread_origin_recovery` 分别给相同完成值、可区别的来源切向与有限深度交比重标后的来源恢复。本节使用同样的“端点值与归一化方向不同”区分，其实际 PDE 估计与取得条件由第25—26节供应，不声称除以消失坐标能增加观测信息。该来源中的几何 blowup 是坐标分辨，和恢复卷第26节的流体奇异性不同。$\square$

**命题 27.3（比值噪声与原始读数的必要误差量级）。** 在正时间实际对 $(s,w)=(r,z)$ 上，若 $|\delta s|\le\epsilon_r<s$、$|\delta w|\le\epsilon_z$，计算比值 $\widetilde\vartheta=\nu(w+\delta w)/(s+\delta s)$ 满足
$$
\widetilde\vartheta-\vartheta
=\frac{\nu\delta w-\vartheta\delta s}{s+\delta s},\qquad
|\widetilde\vartheta-\vartheta|
\le\frac{\nu\epsilon_z+|\vartheta|\epsilon_r}{s-\epsilon_r}.
\tag{27.112}
$$
又 $|\vartheta|\le2Z_*$；$\epsilon_r\le s/2$ 时上界至多 $2(\nu\epsilon_z+2Z_*\epsilon_r)/s$。当 $B_0>0$，仅由一对读数、内部时间未知且没有进一步区分这对候选的档案时，即使第一坐标精确已知，任意确定性参数估计器的最坏误差至少为
$$
\min\{B_0,\nu\epsilon_z/(3s)\}.
\tag{27.113}
$$

证明。通分给（27.112），分母和三角界给所列估计，$\vartheta=\nu V/U$ 给 $2Z_*$。取 $d=\min\{B_0,\nu\epsilon_z/(3s)\}$。参数 $d,-d$ 在各自阈值时间的第二读数相差至多 $6sd/\nu\le2\epsilon_z$，由（25.105）的上界积分可得；第一读数均为 $s$。共同中点同时是两种合法含噪输出，参数相距 $2d$，故至少一个估计误差不小于 $d$。$d=0$ 时下界自然为零。

此两点论证针对仅此原始对的外包合同；若加入旧档案 $C$ 或精确时间旁路，须另证明两候选都在同一个 $K_H$ 中，不能自动把下界限制到任意较小交集。$B_0=0$ 时参数已知，不存在该参数歧义。单个初始原始对 $(0,0)$ 不能计算 $\vartheta(\beta,0)=\beta$；该边界标签需独立提供。提升图的统一稳定性针对提升坐标自身的误差，原始测量转换的 $1/s$ 代价仍在。$\square$

**命题 27.4（准备场上的既有精确因子化及其定量界）。** 置
$$
\mathcal S=\{u_\beta(t):(\beta,t)\in W\},\quad
\mathcal I=\Psi^{-1}:Y\to W,\quad
\mathcal D(a)=u_\beta(t)\ \text{其中 }\mathcal I(a)=(\beta,t),
$$
$$
\mathcal O(U)=(1-2\ell_x(U)/\alpha,-4\ell_y(U)/\alpha).
\tag{27.114}
$$
则 $\mathcal O|_{\mathcal S}$ 与 $\mathcal D$ 互逆。因此任意精确任务 $\mathcal T:\mathcal S\to Z_{\mathcal T}$ 都在实际读数像上有唯一因子 $\mathcal T\circ\mathcal D$；这直接使用既有 [InjectiveInterfaceTargetFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.lean) 的 `injective_interface_factors_every_target` 及 [RealizedImageKernelFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.lean) 的 `realized_image_unique_factorization_iff_reverse_kernel`，不是另立一般解码原理。

具体定量内容为
$$
\|u_\beta(t)-u_{\beta'}(t')\|_2
\le6|\beta-\beta'|+M_F|t-t'|.
\tag{27.115}
$$
对两份原始图坐标，令 $m=\min\{r,r'\}>0$、$P_m=6+4M_FA_1m^2/\nu^3$，则
$$
\|\mathcal D(r,z)-\mathcal D(r',z')\|_2
\le\frac{3\nu P_m}{m}(|z-z'|+L_g|r-r'|)
 +\frac{2M_F}{\nu}|r-r'|.
\tag{27.116}
$$
在提升闭图上，边界标签已给时定义 $\widetilde{\mathcal D}(\widetilde\Psi(\beta,t))=u_\beta(t)$；此时允许 $m=0$，且
$$
\|\widetilde{\mathcal D}(r,v)-\widetilde{\mathcal D}(r',v')\|_2
\le3P_m(|v-v'|+L_s|r-r'|)+\frac{2M_F}{\nu}|r-r'|.
\tag{27.117}
$$

证明。直接有 $\mathcal O(\mathcal D(a))=a$。若 $U=u_\beta(t)\in\mathcal S$，则 $\mathcal O(U)=\Psi(\beta,t)$，图单射给 $\mathcal D(\mathcal O(U))=U$。所以观察在此准备场集合上单射，满足所引现成精确因子化前提。恢复卷（25.106）在共同时间比较参数，恢复卷（25.111）的 $L^2$ 速度界在时间段积分，得（27.115）；没有声称 $H^2$ 时间速度有同一界。代入本卷（25.110）—（25.111）得（27.116），代入（27.108）得（27.117）。提升边界的初态由已给 $\beta$ 决定，定义良好。

任意精确任务可因子化，不意味着它定量稳定。若另外证明 $d_{\mathcal T}(\mathcal T(U),\mathcal T(V))\le L_{\mathcal T}\|U-V\|_2$，才可将这些界乘 $L_{\mathcal T}$；更一般须有自己的 $L^2$ 连续模数。点值、梯度或不连续任务不能自动使用此结论。解码对象是准备场及指定任务，不是整个 $C$ 或取得历史。两数充分也没有证明它们在所有可能传感器或费用合同中全局最优。$\square$

**定理 27.5（续接的定义域等式与自主 PDE 交织）。** 写 $t_*(\beta)=t_\beta(s_*)$，则 $W=\{(\beta,t):|\beta|\le B_0,0<t\le t_*(\beta)\}$。对已知非负内部增量 $\sigma$，定义域子类型上的操作为
$$
\operatorname{Dom}_\sigma=\{a\in Y:\mathcal I(a)=(\beta,t),\quad
 0\le\sigma\le t_*(\beta)-t\},\qquad
\mathcal U_\sigma(a)=\Psi(\beta,t+\sigma).
\tag{27.118}
$$
对任意 $\sigma,\eta\ge0$，
$$
\operatorname{Dom}_{\sigma+\eta}
=\{a\in\operatorname{Dom}_\sigma:\mathcal U_\sigma(a)\in\operatorname{Dom}_\eta\},
\qquad \mathcal U_{\sigma+\eta}=\mathcal U_\eta\circ\mathcal U_\sigma,
\quad\mathcal U_0=\operatorname{id}.
\tag{27.119}
$$
若 $S_\sigma$ 是实际自主 PDE 从该准备场重启的、限制在上述允许域内的续接，则
$$
\mathcal D(\mathcal U_\sigma(a))=S_\sigma(\mathcal D(a))=u_\beta(t+\sigma).
\tag{27.120}
$$
同样的定义与等式适用于边界标签已供给的提升图。

证明。$r$ 在初始分支严格递增，给域的精确形式。两次合法条件分别为 $\sigma\le t_*(\beta)-t$ 和 $\eta\le t_*(\beta)-t-\sigma$，非负增量下它们等价于 $\sigma+\eta\le t_*(\beta)-t$，同时中间时刻必在域内。图逆在第一步后给 $(\beta,t+\sigma)$，代入第二步即得值的复合等式。零步不改变参数或时间，且总在图内合法。移位路径 $q\mapsto u_\beta(t+q)$ 从 $u_\beta(t)$ 解同一自主方程；恢复卷的温和解唯一性将它识别为重启解，证明（27.120）。

对两个都允许同一 $\sigma$ 的图点，推进后参数差及时间差不变，仍在共同 PDE 区间内，故（27.115）仍给相同右界；代入原始输入或提升输入的参数／时间界，（27.116）或（27.117）的原右侧也界定其推进后的场差。这里没有声称实际误差在演化中单调下降。

这些部分操作属于本卷约定1.2和命题1.4的域保持语义；[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) 的 `PartialSignature`、`sourceOperationEquiv` 及 `contextual_equivalence_is_greatest` 已供应域子类型与严格失败传播的形式接口。可将 $\mathcal U_\sigma$ 总化为成功／失败标签，任何失败后的续接仍传播该失败，不返回一个默认场。域外输入与域内却超越剩余时域的非法增量应分别标记；两类都不同于下面的噪声证书未通过。$\square$

**约定 27.6（实际观察者操作保留档案）。** （27.118）是精确图坐标上的数学更新。对完整观察者 $H=(C,\mathcal A,d_{\rm raw})$ 执行操作时，旧 $C$ 逐条保留，当前原始对连同来源、原标签及误差合同保留为旧记录；实际执行的内部推进及新取得动作追加到 $\mathcal A$。若协议确实在推进后取得新的同轨迹双端口对，才把该原始对放入新的 $d_{\rm raw}$，并将其残差与全部旧约束一起加入同一个延伸实现集合。新的相容集合是旧共同实现先经实际操作运输，再与实际新记录约束取交。

若只计算 $\mathcal U_\sigma(a)$、$\mathcal D(a)$ 或预测的新读数，它们只能作为标明的派生值；没有执行推进就不记已推进，没有重新取得就保留最近原始对的原时间标签，不将预测冒充当前测量。两次推进之间取得一次额外记录，会让完整取得历史不同于直接推进一次；（27.119）保证参数、场及合法域的复合等式，不抹去这项历史区别。历史按实际动作序列串接，结合律保留记录次序；只有声明同一个展开协议时，才可将两种动作写法视为同一历史。

严格失败语义至少区分：输入精确值不在图中；共同实现集 $\mathfrak F_H$ 为空；已有精确图点但 $\sigma$ 超过（27.118）的上界；共同实现非空但噪声裕量证书没有通过。前三者均不能通过默认补一个状态继续；第四者表示尚未认证，不能推断实际增量非法。若采用总化编码，这些标签都在其后的严格接续中原样传播。由于 $\mathfrak F_H=\varnothing$ 没有实际见证，即使零步也不能以它认证一个被假定存在的来源；对任意非空相容图集合，零步始终是合法恒等操作。

**定理 27.7（完整相容集合的剩余时域证书）。** 定义
$$
\ell_{\rm rem}(\beta,t)=t_\beta(s_*)-t,\qquad
K_*=4A_1s_*^2/\nu^3.
\tag{27.121}
$$
取定义25.5的一份实际档案相容拟合见证 $\widehat\omega\in\mathfrak F_H$，其投影为 $(\widehat\beta,\widehat t)$。若
$$
\underline r=r_{\rm obs}-\epsilon_r>0,
\quad B_{\rm err}=\frac{6\nu}{\underline r}(\epsilon_z+L_g\epsilon_r),
\quad T_{\rm err}=\frac{4\epsilon_r}{\nu}+K_*B_{\rm err},
$$
$$
E_{\rm adm}=\frac{4\epsilon_r}{\nu}+2K_*B_{\rm err},\qquad
\widehat\ell=\ell_{\rm rem}(\widehat\beta,\widehat t),
\tag{27.122}
$$
则任意两个 $K_H$ 中的候选参数差、时间差分别至多 $B_{\rm err},T_{\rm err}$，剩余时域差至多 $E_{\rm adm}$。因此每个相容候选都允许同一个已知内部增量
$$
0\le\sigma\le\max\{0,\widehat\ell-E_{\rm adm}\}.
\tag{27.123}
$$
推进后实际相容场与拟合续接场满足
$$
\|u_\beta(t+\sigma)-u_{\widehat\beta}(\widehat t+\sigma)\|_2
\le6B_{\rm err}+M_FT_{\rm err}.
\tag{27.124}
$$
该区间仅为充分证书；不能认证某正增量，不证明该增量非法。

证明。阈值时间导数给 $|\partial_\beta t_\beta(s_*)|\le K_*$，故
$$
|\ell_{\rm rem}(\beta,t)-\ell_{\rm rem}(\beta',t')|
\le K_*|\beta-\beta'|+|t-t'|.
\tag{27.125}
$$
先对较大的 $K_{\rm pair}$ 证明界：任意两个候选坐标差至多 $2\epsilon_r,2\epsilon_z$，其较小真实第一坐标满足 $\underline r\le m\le s_*$。定理25.3依次给 $B_{\rm err}$、$4\epsilon_r/\nu+K_*B_{\rm err}$，代入（27.125）给 $E_{\rm adm}$。这些全称界通过 $K_H\subseteq K_{\rm pair}$ 限制到真正档案交集；拟合点具有交集见证，故任意实际相容剩余时域至少 $\widehat\ell-E_{\rm adm}$。正裕量情形可用（27.118）；若该数为负，只保留零步，零步由图域定义独立合法。因此（27.123）在所有情况成立，且从未对负裕量作不合法的正步授权。（27.124）是（27.115）的直接应用。

若实际来源确在初始图上、旧档案相容、同时取得条件成立且共同误差事件为真，则真实实现在 $\mathfrak F_H$，证书便约束真实动作。若交集空，或拟合只属于 $K_{\rm pair}$ 而无共同档案见证，不能称此证书已对完整观察者实例化。测得原始对不在精确图像中，并不自动使交集空；噪声情形须用残差判断。一个数值实现可以将 $\widehat\ell$ 换成其认证下界，但计算该下界与提供拟合见证仍有独立成本。

每个候选推进后的剩余时域都严格减去同一个 $\sigma$，与拟合的剩余时域差不变。因此对未新增测量的传播候选集，所有累计增量不超过原正裕量的序列继续被同一个 $E_{\rm adm}$ 支持；（27.119）给域与值的复合。实际新增记录只在同一延伸实现上进一步取交，不能重新挑一个不兼容的来源来维持拟合。

$B_0=0$ 时参数已知，可令 $B_{\rm err}=0$、$T_{\rm err}=E_{\rm adm}=4\epsilon_r/\nu$；$r_t\ge\nu/2$ 直接界定任意两候选的时间差，此单点版本可包含已知初始时刻且无需 $\underline r>0$。非空共同见证仍必需。对于非单点参数，正下界失败只表明（27.122）不能使用，不等于实际离开图域或正增量非法。$\square$

**注记 27.8（内部续接、来源标签与关系范围）。** 所有续接都要求已知内部时长 $\sigma$；未知共同钟下等待一个指定外部时长并不提供它，须另有时钟运输或实际取得证书。修改初态、外力、黏性、校准或测量干预是另一种操作，不能沿用当前的闭合域。越过 $t_*(\beta)$ 未获本接口许可，即使 PDE 本身仍可继续也一样。

在这里声明的自主非负推进下，恢复出的来源标签 $\beta$ 不变、内部时间平移；相同 $\beta$ 的两图点依时间顺序由一个允许前进量连接，不同 $\beta$ 则不能由这些操作连接。这是相对于规定操作的轨道标签，完整场仍随时间变化；它不表示所有空间场静止，也不把时间从空间推出。比值边界只是改变表示与误差几何，既不供应初始原始对所缺的标签，也不分配概率。

全场解码及响应逆的存在不使其求值免费：所需实际 PDE 求解、逆响应认证、端口取得、阈值监测、钟可达性和档案共同见证各有原来的资源条件。本文的数学陈述是普通证明，适用范围为固定准备族的共同短时图；有限维、全 PDE、精确识别、稳定性、合法操作和完整已获档案分别由各自明确条件承担。

## 27.99 追加锚

## 28. 有向初始图、三阶识别与黏性纤维

**定义 28.1（校准尺度与参数任务）。** 固定有符号且已校准的 $\alpha\ne0$，采用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义27.1的实际无外力 PDE、同源准备和端口。用
$$
p=(m,k)=\left(\frac\beta\nu,\frac{\alpha^2}{\nu^2}\right),\quad k>0,
\qquad \nu(p)=\frac{|\alpha|}{\sqrt k},\quad
\beta(p)=\frac{m|\alpha|}{\sqrt k}
\tag{28.101}
$$
作为参数坐标；它与 $(\beta,\nu)\in\mathbb R\times(0,\infty)$ 光滑互逆。$p$ 不表示流体压力。本节的图关系是同一实际轨迹上 $r_p(t)=1-2x_p(t)/\alpha$、$z_p(t)=-4y_p(t)/\alpha$ 所形成的有向初始关系。所有已获时间戳、钟限制、准备与旧档案关系仍按定义25.5保留；这里消去时间参数只为识别 $(\beta,\nu)$ 及指定准备场任务。

**定理 28.2（参数依赖的初始逆时间）。** 在任意紧参数集 $K$ 的开邻域内，缩短恢复卷的共同 $H^{12}$ 时间后，存在共同 $T_g,r_*>0$，使 $0\le r\le r_*$ 有唯一初始分支时间 $t_p(r)\in[0,T_g]$。函数 $t(p,r)$ 及
$$
g(p,r)=z_p(t_p(r)),\qquad g(p,0)=0
\tag{28.102}
$$
联合 $C^5$ 至 $r=0$，且对 $\xi=m,k$ 有
$$
\partial_rt_p(r)=\frac1{\partial_tr_p(t_p(r))},\qquad
\partial_\xi t_p(r)=-\frac{\partial_\xi r_p(t_p(r))}{\partial_tr_p(t_p(r))}.
\tag{28.103}
$$

证明。恢复卷定理27.3—27.4给联合 $C^5$ 的真实端口及 $r_t(p,0)=\nu(p)>0$。在 $K$ 的稍大紧邻域取 $\nu_{\min}>0$；联合连续性允许同一 $T_g\le T_{12}$ 使 $r_t\ge\nu_{\min}/2$。可取 $r_*\le\nu_{\min}T_g/4$，介值定理和严格单调性给唯一逆，且正端点离 $T_g$ 留有裕量。

为使用普通开域逆函数定理，在负时间把每个端口延成其零点的五次 Taylor 多项式。恢复卷（27.111）说明各初始系数对参数光滑；正时间的全部所需混合导数连续至零，所以正负两侧在总阶至多五的导数上相合，得到联合 $C^5$ 延拓。它只是一种函数延拓，绝非负时间 PDE 解。对 $(p,t)\mapsto(p,r_p(t))$ 使用逆函数定理，$r_t>0$ 给可逆导数；局部逆由单调性一致拼接，限制回非负 $r$ 得所需函数。对 $r_p(t_p(r))=r$ 求导得到（28.103），再复合真实 $z$ 得 $g$。这同时供应连续的 $\partial_m\partial_r^4g,\partial_k\partial_r^4g$：参数微分逆时间可出现第五时间导数，已由恢复卷供应，没有对外部未知钟求导。

普通逆函数步骤的钉版直接供应者是 Mathlib 的 [InverseFunctionTheorem/ContDiff.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean) 中 `ContDiffAt.toOpenPartialHomeomorph`、`ContDiffAt.localInverse`、`ContDiffAt.to_localInverse`；这些有限维逆接口不承担恢复卷的 PDE 正则性。$\square$

**定理 28.3（精确三阶图像及其逆）。** 令 $g_j=\partial_r^jg(p,0)$。全部实际准备满足
$$
g_1=m,\qquad g_2=F(m):=-\frac{m(m^2+30)}{10},\qquad
g_3=G(m,k):=\frac m{100}(3m^4+95m^2+300-10k).
\tag{28.104}
$$
在 $\beta\ne0,\nu>0$ 上，三阶图射流全局单射到其精确像。给定 $(m,j_2,j_3)$ 属于此非退化像，当且仅当
$$
m\ne0,\qquad j_2=F(m),\qquad
Q=\frac{3m^4+95m^2+300}{10}-\frac{10j_3}{m}>0.
\tag{28.105}
$$
其唯一逆为 $k=Q,\nu=|\alpha|/\sqrt Q,\beta=m|\alpha|/\sqrt Q$；另有参数先验时还须检查逆值落在先验内。前两阶图射流不能在此二维参数族中识别黏性。

证明。在 $z_p(t)=g(p,r_p(t))$ 中求三次实际时间导数，得到
$$
g_1=\frac{z_t(0)}{r_t(0)},\quad
g_2=\frac{z_{tt}(0)-g_1r_{tt}(0)}{r_t(0)^2},\quad
g_3=\frac{z_{ttt}(0)-g_1r_{ttt}(0)-3g_2r_t(0)r_{tt}(0)}{r_t(0)^3}.
\tag{28.106}
$$
代入恢复卷（27.114）给（28.104）；解第三式给 $Q=k$。反之，（28.105）定义正黏性和非零 $\beta$，代回全部三式正好复现供给的射流，证明必要与充分。此为有限射流相容性，不保证任意带有该射流的整条曲线都来自 PDE。$Q\le0$ 不能实现为有限正黏性，不能静默投影至正数；$m=0$ 不在除法公式域内。

固定任何非零 $m$，$(\beta,\nu)=(m\nu,\nu)$ 随正 $\nu$ 改变时 $g_1,g_2$ 相同，$g_3$ 随 $\alpha^2/\nu^2$ 改变。任意含两点的这类局部线段已给前两阶不足；最小阶数的结论只针对准备初点的这些图射流，不比较任意有限传感器协议。逆在 $m\ne0,Q>0$ 上光滑，局部 Lipschitz，离这两条退化边界有正距离的紧射流域上可取统一常数；特别
$$
\frac{\partial Q}{\partial j_3}=-\frac{10}{m},\qquad
\frac{\partial\nu}{\partial j_3}=\frac{5|\alpha|}{mQ^{3/2}}.
\tag{28.107}
$$
故不能跨越 $\beta=0$ 声称统一稳定性。

在固定校准的 Euclidean 端口平面，曲率只是这些导数的另一表达：
$$
\kappa_0=\frac{F(m)}{(1+m^2)^{3/2}},\qquad
\frac{d\kappa}{d\ell}(0)=\frac{G(m,k)}{(1+m^2)^2}
 -\frac{3mF(m)^2}{(1+m^2)^3}.
\tag{28.108}
$$
这里 $\ell$ 是沿增大 $r$ 的弧长；由 $\kappa=g''/(1+g'^2)^{3/2}$ 及 $d/d\ell=(1+g'^2)^{-1/2}d/dr$ 直接求导。初始曲率已由切向 $m$ 决定，曲率变化才携带第三阶信息；这没有增加一个状态或一次测量，也不声称对任意端口重校准不变。$\square$

**引理 28.4（一次统一的混合四阶图余项）。** 在定理28.2的较小紧参数邻域和共同 $[0,r_*]$ 上，定义
$$
R(p,r)=g(p,r)-mr-\tfrac12F(m)r^2-\tfrac16G(m,k)r^3.
\tag{28.109}
$$
对 $a=0,m,k$，记 $D_0$ 为恒等、$D_m=\partial_m,D_k=\partial_k$，并令 $M_a=\sup|D_a\partial_r^4g|<\infty$。则
$$
D_aR(p,r)=\frac16\int_0^r(r-v)^3D_a\partial_r^4g(p,v)\,dv,
\qquad |D_aR(p,r)|\le\frac{M_a}{24}r^4.
\tag{28.110}
$$
因此 $g=mr+F(m)r^2/2+G(p)r^3/6+O_{C^1(p)}(r^4)$，一致地有
$$
\partial_mg(p,r)=r+O(r^2),\qquad
\partial_kg(p,r)=-\frac m{60}r^3+O(r^4).
\tag{28.111}
$$

证明。对 $g$ 使用四阶积分 Taylor 公式，定理28.3给零至三阶系数。定理28.2的联合 $C^5$ 保证对参数在积分下微分合法且混合导数交换，得到同一公式的 $D_m,D_k$ 版本。$\int_0^r(r-v)^3dv=r^4/4$ 给常数 $1/24$；紧性给有限的 $M_a$。最后对系数求导，$G_k=-m/10$，即得（28.111）。后文的有限记录和有限差分共用此余项，不另假定解析性。积分 Taylor 的钉版直接供应者是 Mathlib [Taylor.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Taylor.lean) 的 `taylor_integral_remainder`、`taylor_mean_remainder_bound`；这里的 $1/24$ 来自所展示的积分而非额外经验常数。$\square$

**推论 28.5（履行命题26.4的黏性前提）。** 固定 $\alpha\ne0$ 和 $(\beta_0,\nu_0)$ 的正黏性内点邻域。实际 PDE 满足命题26.4（26.113）的全部统一渐近。因而在 $\beta_0\ne0$ 的内点，一份足够短正内部时间的同时端口对，仍有该命题所述随 $\nu$ 变化的精确局部 $(\beta(\nu),t(\nu))$ 纤维，且（26.114）的两导数均非零。

证明。恢复卷定理27.2—27.4给开参数域上的光滑性及初始恒等式。对这些初值作参数微分：$r_\nu(0)=r_\beta(0)=z_\nu(0)=z_\beta(0)=0$，而 $r_{\nu t}(0)=1,r_{\beta t}(0)=z_{\nu t}(0)=0,z_{\beta t}(0)=1$。在紧邻域上二阶时间导数及其参数导数一致有界，Taylor 积分式遂给
$$
r_\nu=t+O(t^2),\quad z_\nu=O(t^2),\quad
r_t=\nu+O(t),\quad z_t=\beta+O(t),\quad
r_\beta=O(t^2),\quad z_\beta=t+O(t^2).
\tag{28.112}
$$
这正是继承的（26.113）；直接应用命题26.4的条件纤维结论，无需第二次一般隐函数证明。固定充分小 $t>0$ 后，$-t/\nu+O(t^2)$ 和 $\beta/\nu+O(t)$ 在非零 $\beta$ 内点均非零。旧命题的原条件文本仍成立，此处履行其当时尚缺的实际黏性正则性前提。

纤维首先属于单份读数的参数／时间任务载体；要把其中两点称为完整观察者不可区分，仍须使同一完整旧档案、所记时间戳和允许钟关系各有对应的完整实现。已知内部时间或其它旧记录可切开此纤维。本推论不把它变成任何传感器数的普遍最优性断言。$\square$

**命题 28.6（剪切边界与幅度、黏性、时间的共同缩放）。** 非退化识别保留如下精确边界。$\beta=0$ 的整个图恒为 $z=0$，不同正黏性的未知钟碰撞由命题26.4（26.112）给出；$\alpha=0$ 的原始双端口历史恒零，由恢复卷命题25.7（25.120）的不可见剪切给出。这两项直接复用既有精确解及证明。$\nu=0$ 时 $r_t(0)=0$，本节的正则图逆前提失效，并无由本证明得到的无黏性结论。

如果准备幅度绝对尺度未知，则对任意 $c>0$，实际 PDE 有缩放
$$
u^c(t,X)=c\,u(ct,X),\quad \Pi^c(t,X)=c^2\Pi(ct,X),\qquad
(\alpha,\beta,\nu)\mapsto(c\alpha,c\beta,c\nu),
$$
$$
r^c(t)=r(ct),\qquad z^c(t)=z(ct).
\tag{28.113}
$$
此外 $X\mapsto X+(\pi,\pi)$ 将 $\alpha$ 变为 $-\alpha$ 而保持 $\beta$；原始双端口都变号，归一化图保持。故仅无参数化归一化图的三阶非退化射流给 $\beta/\nu$ 和 $|\alpha|/\nu$，不提供三者的绝对尺度或 $\alpha$ 的符号。

证明。缩放后的时间导数、对流、黏性项和压力梯度都是原方程对应项的 $c^2$ 倍，初态正好具有所列幅度；归一化抵消外侧 $c$。平移对初始可见余弦给负号、对 $X_2-X_1$ 模态给正号；方程平移不变及唯一性延伸此关系，两读出模态的相位均为 $-1$，所以所列端口关系对整条实际轨迹成立。

若允许未知共同传感器增益 $a_g$，将它改为 $a_g/c$ 并把候选钟改成原钟的 $1/c$，便与（28.113）一同保留全部这些原始测量值；额外档案约束仍须逐项满足。相反，若初始校准原始读数 $x(0)$ 已实际取得，$\alpha=2x(0)$ 供应有符号尺度，无需再次免费给一项测量。此陈述不含新的含噪 $\alpha$ 联合逆定理。独立未知增益、丢失空间相位、异步端口、缺失初始准备点、改变初态族或扰动演化的测量，均不满足本节合同，须各自解决识别与共同轨迹合法性。$\square$

**推论 28.7（图访问、已获样点时间及既有因子化的任务域）。** 设共同外部钟 $\theta$ 连续严格递增、$\theta(0)=0$，同源且同时的端口读数为 $(r_p(\theta(s)),z_p(\theta(s)))$。若实际访问到零点附近任意小正内部时间，观察到的有向图 germ 就是 $g_p$；此结论无需 $\theta$ 可微或有正导数。三阶射流识别之后，对任一已获且有初始分支证书的样点 $(s_i,r_i,z_i)$，唯一内部时间和准备场分别为
$$
\theta(s_i)=t_p(r_i),\qquad u_p(t_p(r_i)).
\tag{28.114}
$$
只有这些实际已获样点的钟值由此确定，不确定未采样钟插值，更不重建或商掉完整档案。

证明。$r_t>0$ 和 $\theta$ 的连续严格单调性保留图与方向，零点相连的小正访问保留 germ。对已识别参数应用定理28.2的单调逆，得到（28.114）。有初始跳跃的钟不必提供 germ；没有到达指定正阈值的钟也不提供该记录。

精确图射流属于理想访问，不是免费有限记录。即便确实取得 $r=0,h,2h,3h$、且 $g(0)=0$ 精确，第三前向差分 $[g(3h)-3g(2h)+3g(h)]/h^3$ 在三个非初始标量各有误差 $\epsilon$ 时仅噪声项已有 $7\epsilon/h^3$ 界；截断偏差还需四阶导数，位置误差另计。第29节另给两份实际记录的局部结论。

对一个选定的参数邻域，以参数 $p$ 为载体，精确射流接口由定理28.3单射；若要解码已获样点的准备场，则载体取带这些实际 $r_i$ 的 $(p,(r_i)_i)$，接口同时保留射流与 $(r_i)_i$，仍单射。直接应用既有 [InjectiveInterfaceTargetFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.lean) 的 `injective_interface_factors_every_target`，或 [RealizedImageKernelFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.lean) 的 `realized_image_unique_factorization_iff_reverse_kernel`，可因子化参数与这些指定准备场任务。此单射前提不施于含任意钟和旧记录的完整实现集合；后者可有多个实现共享同一参数任务。任务的稳定性、求值资源和新操作合法性仍须各自的界。

共同钟消去沿用定理21.2与命题23.4—推论23.5的任务区别，初始方向与端点值的区别沿用第27节及 [GoldenThreadBlowup](../../../D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.lean)。成熟的初始输出／Lie 导数方法见 Sontag, *Dynamic compensation, parameter identifiability, and equivariances*, PLOS Computational Biology（2017），[作者原文](https://www.sontaglab.org/FTPDIR/dynamic_compensation_parameter_identifiability_equivariances_sontag_plos2017.pdf)第5—6页；这里仅使用有限阶导数，不假定解析性，也不从所有 Taylor 系数相同反推一般光滑轨迹相同。[FiniteCrystalTimeFrequencyBridge](../../../D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.lean) 的 `first_crystal_time_window_injective` 与 [FinitePronyNodeIdentification](../../../D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification.lean) 的 `recurrence_window_identifies_node_roots` 要求其有限指数模态模型；这里没有这种不变模态前提。[ProjectiveJetScaleInvariance](../../../D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance.lean) 处理常值输出尺度，[PairCalibratedSecondMagnusObservability](../../../D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability.lean) 允许各对不同时间，均不替代此处的共同阈值与全 PDE 桥梁。$\square$

## 29. 两份有限记录的统一逆、取得资源与受限实验下界

**定义 29.1（一个完整实现集合上的两份记录）。** 继续定义25.5、第27节的完整观察者语义，现在令 $\Omega$ 中的每份实现 $\omega$ 同时包含来源身份、固定已校准 $\alpha$、参数 $p(\omega)=(m,k)$、由同一准备生成的实际轨迹 $u_p$、一个允许的连续严格递增钟 $\theta_\omega$，以及解释全部旧记录、误差和关系的辅助量。完整已获信息写为 $H=(C,\mathcal A,D_1,D_2)$：$C$ 保留全部先前内部／外部记录及关系，$\mathcal A$ 保留合法动作、端口、校准、分支和共同轨迹证书，$D_j=(s_j,\widetilde r_j,\widetilde z_j)$ 是两份有序实际同时记录，$s_1<s_2$ 是保留的外部时间戳。对已声明局部先验 $U$ 和第28节初始图域，令 $t_j(\omega)=\theta_\omega(s_j)$、$r_j(\omega)=r_{p(\omega)}(t_j(\omega))$，定义
$$
\begin{aligned}
\mathfrak F_H=\{\omega\in\Omega:\;&p(\omega)\in U,\quad
\operatorname{Hist}(\omega,\mathcal A),\quad
\mathcal R_i(\omega,c_i)\ \text{对全部 }c_i\in C,\\
&\omega\in\mathcal E_H,\quad
0<t_1(\omega)<t_2(\omega)\le T_g,\quad
0<r_1(\omega)<r_2(\omega)\le r_*,\\
&|r_j(\omega)-\widetilde r_j|\le\epsilon_r,\quad
|g_{p(\omega)}(r_j(\omega))-\widetilde z_j|\le\epsilon_z\quad(j=1,2)\},\\
\mathcal K_H&=\{p(\omega):\omega\in\mathfrak F_H\}.
\end{aligned}
\tag{29.101}
$$
$\mathcal E_H$ 是一份联合误差事件，可施加相关性和其它旧限制，不预设独立噪声。旧钟校准、同源关系或额外传感器均仍在 $\mathcal R_i$ 内；不能为两份记录或各条旧约束另选互不相容的实现。若测量由原始 $x,y$ 换算，则在同一联合事件上严格使用
$$
\epsilon_r=\frac{2\epsilon_x}{|\alpha|},\qquad
\epsilon_z=\frac{4\epsilon_y}{|\alpha|}.
\tag{29.102}
$$
这里 $\alpha$ 固定且已校准。精确事件是误差为零且 $r_j=j\eta$ 的特例；两记录和校准初点均仍附于完整档案。模型预测不替代实际取得，重开缓存第一记录不产生第二记录。

**定理 29.2（两精确阈值的局部识别与三次病态量级）。** 固定 $p_0=(m_0,k_0)$，$m_0\ne0,k_0>0$。对充分小 $\eta>0$，两份已实际取得的初始分支精确阈值响应定义
$$
\mathcal O_\eta(p)=(g_p(\eta),g_p(2\eta)).
\tag{29.103}
$$
它在 $p_0$ 附近有 $C^1$ 局部逆，且
$$
\det D\mathcal O_\eta(p_0)=-\frac{m_0}{10}\eta^4+O(\eta^5),
\qquad \|(D\mathcal O_\eta(p_0))^{-1}\|_2=\Theta(\eta^{-3}).
\tag{29.104}
$$

证明。仅用引理28.4的一致混合余项，$\partial_mg(r)=r+O(r^2)$，$\partial_kg(r)=-mr^3/60+O(r^4)$，故
$$
\det D\mathcal O_\eta
 =(\eta+O(\eta^2))\left(-\frac{8m}{60}\eta^3+O(\eta^4)\right)
 -(2\eta+O(\eta^2))\left(-\frac m{60}\eta^3+O(\eta^4)\right)
 =-\frac m{10}\eta^4+O(\eta^5).
\tag{29.105}
$$
非零 $m_0$ 使充分小正 $\eta$ 时行列式非零，有限维逆函数定理给局部逆。若 $|\det D\mathcal O_\eta+m_0\eta^4/10|\le C_D\eta^5$，$C_D>0$ 时附加 $\eta\le|m_0|/(20C_D)$ 就足以保留非零性；还须满足共同图域限制。第一参数列为 $(\eta,2\eta)+O(\eta^2)$，故大奇异值有上下界常数乘 $\eta$；奇异值乘积为行列式绝对值，给小奇异值为常数乘 $\eta^3$，从而得到逆导数的精确量级。

此为局部两记录逆；定理28.3在其精确三阶射流像上的全局逆并不把这里升级为任意参数盒上的全局两样点逆。精确阈值仍须实际取得，同一完整见证仍须满足定义29.1。把导数识别转成有限样点的 Taylor／Vandermonde、余项与最小奇异值方法，见 Sontag, *A concept of local observability*, Systems & Control Letters 5（1984），41–47，[作者原文](https://www.sontaglab.org/FTPDIR/localobs.pdf)，Lemma 3.4（第44页）及 Section 4 的证明（第45—46页），Lemma 3.5 使用逆函数定理。该文对象是有限维受控系统；这里的全 PDE 参数正则性、阈值图及特定系数分别由恢复卷第27节和本卷第28节承担，不由该有限维结果直接推出。$\square$

**定理 29.3（显式预条件与一个固定凸参数邻域）。** 令 $F,G$ 如（28.104），已知位置比的设计域为
$$
\mathcal D=[3/4,5/4]\times[7/4,9/4],\qquad (\lambda,\mu)\in\mathcal D.
\tag{29.106}
$$
对 $3\eta\le r_*$ 定义
$$
A_{\eta,\lambda}(p)=\frac{g_p(\lambda\eta)}{\lambda\eta},
$$
$$
B_{\eta,\lambda,\mu}(p)=\frac1\eta\left[
 \frac{2\{g_p(\mu\eta)-(\mu/\lambda)g_p(\lambda\eta)\}}
 {\mu(\mu-\lambda)\eta^2}-F(A_{\eta,\lambda}(p))\right],\qquad
\mathcal P_{\eta,\lambda,\mu}=(A_{\eta,\lambda},B_{\eta,\lambda,\mu}).
\tag{29.107}
$$
存在一个固定闭凸球 $U=\overline B(p_0,\rho)$、共同 $\eta_0>0,K<\infty$，使对所有 $p,q\in U,(\lambda,\mu)\in\mathcal D,0<\eta\le\eta_0$，
$$
\|\mathcal P_{\eta,\lambda,\mu}(p)-\mathcal P_{\eta,\lambda,\mu}(q)\|_2
 \ge\frac{\|p-q\|_2}{2K}.
\tag{29.108}
$$
球 $U$ 在参数空间，不是与 $\eta$ 无关的原始输出球。

证明。固定正 $\eta,\lambda,\mu$ 时，（29.107）是两个输出 $z_1,z_2$ 的可逆变换：$z_1=\lambda\eta A$，
$z_2=(\mu/\lambda)z_1+\mu(\mu-\lambda)\eta^2[F(A)+\eta B]/2$。它只重表达两条既有记录，不增加测量。

引理28.4给一致于 $\mathcal D$ 的 $C^1(p)$ 展开
$$
A=m+\frac\lambda2F(m)\eta+O_{C^1}(\eta^2),\qquad
\mathcal P_{\eta,\lambda,\mu}\longrightarrow
\mathcal P_{0,\lambda,\mu}=(m,J_{\lambda,\mu}(m,k)),
$$
$$
J_{\lambda,\mu}=\frac{\lambda+\mu}{3}G(m,k)-\frac\lambda2F'(m)F(m),
\qquad \partial_kJ_{\lambda,\mu}=-\frac{(\lambda+\mu)m}{30}.
\tag{29.109}
$$
收敛的 $C^1$ 误差为 $O(\eta)$。确实，$B$ 方括号中首项展开成
$F(m)+(\lambda+\mu)G\eta/3+O_{C^1}(\eta^2)$，而
$F(A)=F(m)+\lambda F'(m)F(m)\eta/2+O_{C^1}(\eta^2)$；相减除以 $\eta$ 即得。多项式 $F$ 及一致 $C^1$ 余项保证参数导数亦有相同阶数。

令
$$
L_{\lambda,\mu}=D\mathcal P_{0,\lambda,\mu}(p_0),\qquad
K=\max_{(\lambda,\mu)\in\mathcal D}\|L_{\lambda,\mu}^{-1}\|_2.
\tag{29.110}
$$
$L$ 第一行为 $(1,0)$，行列式为 $-(\lambda+\mu)m_0/30\ne0$；连续性和紧性给 $0<K<\infty$。在共同开图参数域内选择
$0<\rho<\min\{|m_0|/2,k_0/2\}$，使闭球 $U$ 连同邻域留在该域，且
$$
K\sup_{p\in U,(\lambda,\mu)\in\mathcal D}
 \|D\mathcal P_{0,\lambda,\mu}(p)-L_{\lambda,\mu}\|_2\le\tfrac14.
\tag{29.111}
$$
这由紧设计域上的一致连续性实现。再用一致 $C^1$ 收敛选择 $0<\eta_0\le\min\{1,r_*/3\}$，使
$$
K\sup_{p\in U,(\lambda,\mu)\in\mathcal D}
 \|D\mathcal P_{\eta,\lambda,\mu}(p)-D\mathcal P_{0,\lambda,\mu}(p)\|_2
 \le\tfrac14\quad(0<\eta\le\eta_0).
\tag{29.112}
$$
若一致 $C^1$ 余项界为 $C_R\eta$，$C_R>0$ 时还可用 $\eta_0\le1/(4KC_R)$。这些给定的是导数界的充分条件和有限常数的存在，不给未经计算的数值 PDE 半径。

两项四分之一界合成 $\sup_U\|L^{-1}D\mathcal P_\eta-I\|_2\le1/2$。对 $p,q\in U$，整条直线段在 $U$ 中，故
$$
L^{-1}(\mathcal P_\eta(p)-\mathcal P_\eta(q))
 =(p-q)+\int_0^1(L^{-1}D\mathcal P_\eta(q+s(p-q))-I)(p-q)\,ds.
\tag{29.113}
$$
右侧范数至少 $\|p-q\|_2/2$，左侧至多 $K\|\mathcal P_\eta(p)-\mathcal P_\eta(q)\|_2$，得（29.108）。这一步把点态导数条件提升为统一非线性比较；固定 $U$ 不随 $\eta$ 缩小，其实际预条件输出像上的逆 Lipschitz 常数至多 $2K$。原始输出的误差仍被（29.107）的 $\eta$ 分母放大。$\square$

**定理 29.4（已获含噪记录的完整可行集直径）。** 使用定理29.3的同一个 $U,\eta_0$，取 $0<\eta\le\eta_0$。实际测得位置满足
$$
\widetilde r_1\in[3\eta/4,5\eta/4],\qquad
\widetilde r_2\in[7\eta/4,9\eta/4],\qquad
0\le\epsilon_r\le\eta/8.
\tag{29.114}
$$
取实际记录的固定设计比 $\lambda=\widetilde r_1/\eta,\mu=\widetilde r_2/\eta$。令
$$
L_g=\sup_{p\in U,0\le r\le r_*}|\partial_rg_p(r)|,\quad
e=\epsilon_z+L_g\epsilon_r,\quad
C_F=\sup_{|v|\le L_g}|F'(v)|=3+\tfrac3{10}L_g^2,
$$
$$
C_T=\sqrt{(4/3)^2+(64/7+4C_F/3)^2}.
\tag{29.115}
$$
对完整可行集 $\mathcal K_H$ 中任意两候选 $p,q$，都有
$$
\|p-q\|_2\le4Ke\left[
\frac1{\lambda^2\eta^2}
 +\left\{\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
             +\frac{C_F}{\lambda\eta^2}\right\}^2\right]^{1/2},
\tag{29.116}
$$
$$
\|p-q\|_2\le\min\left\{2\rho,\frac{4KC_Te}{\eta^3}\right\}.
\tag{29.117}
$$
若一个真实完整实现同时满足全部旧约束、取得历史和两条新原始误差约束，则 $\mathfrak F_H\ne\varnothing$；此时对任意有完整见证的拟合 $q$ 与真实参数 $p_*$，同一界给 $\|q-p_*\|_2$。

证明。任何候选的真实 $r$ 值落在互不相交的正区间 $[5\eta/8,11\eta/8]$ 和 $[13\eta/8,19\eta/8]$，均含于 $[0,r_*]$，因为 $3\eta\le r_*$。窗口本身不证明同源或第一分支，这两项由定义29.1的见证承担。沿图坐标用中值定理，得到
$$
|g_p(\widetilde r_j)-\widetilde z_j|\le e\quad(j=1,2).
\tag{29.118}
$$
故任意两候选在这两个固定测得位置的精确预测值各相差至多 $2e$。$g_p(0)=0$ 还给 $|A_{\eta,\lambda}(p)|\le L_g$。将（29.107）用于两组精确预测，用 $F$ 的中值界得到
$$
|\Delta A|\le\frac{2e}{\lambda\eta},\qquad
|\Delta B|\le2e\left[
\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
 +\frac{C_F}{\lambda\eta^2}\right].
\tag{29.119}
$$
与（29.108）合用即得（29.116）。设计域给 $\lambda\ge3/4,\mu\ge7/4,\mu-\lambda\ge1/2,\mu/\lambda\le3$；再用 $\eta\le1$ 得 $C_T/\eta^3$ 的上界。$p,q\in\overline B(p_0,\rho)$ 给直径上限 $2\rho$。这些是整个完整可行集的成对界，无需噪声记录本身位于精确模型像内。

一个真实完整见证才保证非空；只对新对成立的原始误差假设至多保证对记录外包集合非空，不保证与旧档案交集非空。若 $\mathfrak F_H$ 为空，本定理不产生拟合参数，不能用静默投影替代；空集上的全称界也不授权后续操作。较强旧约束只缩小可行集，仍保留上界。已知的测得位置偏移属于这份设计，只有未确定的真实 $r$ 偏差由 $\epsilon_r$ 计入噪声。

因此请求参数坐标误差 $\delta>0$ 时，一个明确充分精度条件为
$$
\epsilon_z+L_g\epsilon_r\le\frac{\delta\eta^3}{4KC_T},\qquad
\epsilon_r\le\eta/8,
\tag{29.120}
$$
同时保留局部先验、同源第一分支和非空完整见证。为转换物理参数，令 $k_{\min}=\min_Uk>0,M_m=\max_U|m|$，
$$
N=\frac{|\alpha|}{\sqrt{k_{\min}}},\qquad
C_\nu=\frac{|\alpha|}{2k_{\min}^{3/2}}.
$$
$$
|\nu(p)-\nu(q)|\le C_\nu|k_p-k_q|,\qquad
|\beta(p)-\beta(q)|\le N|m_p-m_q|+M_mC_\nu|k_p-k_q|.
\tag{29.121}
$$
第一式由 $k^{-1/2}$ 的中值定理，第二式由 $m_p\nu_p-m_q\nu_q=\nu_p(m_p-m_q)+m_q(\nu_p-\nu_q)$。代入（29.117）给黏性及隐藏幅度的实际误差界。$g_q(\widetilde r_j)$ 是核对候选的预测，不是另一条取得记录；新增记录仍取同一个完整实现集合的交集。

精确两记录在 $U$ 上单射后，对参数载体或带已获 $r_i$ 的准备场载体，直接应用推论28.7所引现成因子化结果。它不声称对整个 $\Omega$ 单射，不消除已保留钟信息，也不赋予含噪档案一个精确一般解码器。$\square$

**定理 29.5（内部阈值成本与条件外部期限）。** 在固定实际校准 $\alpha$ 的局部先验上，选界
$$
0<a\le|\alpha|\le A,\qquad 0<b\le|\beta|\le B,\qquad
0<\nu_{\min}\le\nu\le\nu_{\max}.
\tag{29.122}
$$
取恢复卷第25节的同一 $H^2$ 常数在此参数域上的上包络
$$
R=2\sqrt{2A^2+9B^2},\quad \tau_*=\frac{\nu_{\min}}{16384R^2},\quad
M_*=(\nu_{\max}+R)(\nu_{\max}R+4R^2),\quad D_*=\frac{2M_*}{a},
$$
$$
T_*=\min\left\{\tau_*,\frac{\nu_{\min}}{2D_*}\right\},\qquad
T_c=\min\{T_{12},T_g,T_*\},\qquad
0<\eta\le\min\left\{\eta_0,\frac{\nu_{\min}T_c}{4}\right\}.
\tag{29.123}
$$
其中 $T_{12}$ 来自恢复卷的开参数族，$T_g,r_*$ 来自定理28.2，$\eta_0\le r_*/3$ 来自定理29.3，均在同一稍大参数邻域上选择。则两个精确初始阈值有唯一内部时刻 $0<t_1<t_2\le T_c$，且
$$
\frac{2j\eta}{3\nu}\le t_j\le\frac{2j\eta}{\nu},\qquad
\frac{2j\eta}{3\nu_{\max}}\le t_j\le\frac{2j\eta}{\nu_{\min}}\quad(j=1,2),
$$
$$
\frac{2\eta}{3\nu}\le t_2-t_1\le\frac{2\eta}{\nu},\qquad
 t_2\le\frac{4\eta}{\nu_{\min}}.
\tag{29.124}
$$
若允许钟另满足下增量率 $c>0$，即
$$
\theta(s')-\theta(s)\ge c(s'-s)\quad(0\le s<s'\le S),
\tag{29.125}
$$
且钟和实际同时事件取得接口可用至 $S_*=4\eta/(c\nu_{\min})$，则两个精确阈值事件均在该外部期限内可达；其外部时刻满足
$$
s_j\le\frac{2j\eta}{c\nu}\le\frac{2j\eta}{c\nu_{\min}},\qquad
s_2-s_1\le\frac{2\eta}{c\nu}\le\frac{2\eta}{c\nu_{\min}}.
\tag{29.126}
$$

证明。恢复卷定理25.3、25.6给 $[0,\tau_*]$ 上同一 $H^2$ 解及 $|x_{tt}|\le M_*$；与恢复卷定理27.2的解由唯一性一致。故 $|r_{tt}|\le D_*$，从 $r_t(0)=\nu$ 积分，在 $[0,T_*]$ 得
$$
|r_t(t)-\nu|\le D_*t\le\nu_{\min}/2\le\nu/2,\qquad
\nu/2\le r_t(t)\le3\nu/2,\quad
\nu t/2\le r(t)\le3\nu t/2.
\tag{29.127}
$$
$\beta$ 的正下界只用于非退化识别，此取得计算也适用于 $\beta=0$。$r(T_c)\ge\nu_{\min}T_c/2\ge2\eta$，连续严格单调性给两个唯一内部 hit；将（29.127）分别在零点至 hit 及两 hit 之间积分，得到（29.124）。$T_c$ 与 $\eta_0$ 的交集使 $H^{12}$ 正则、图逆、非线性参数逆和 $H^2$ 取得界在同一实验同时有效。

对任意定义在 $[0,S]$ 的连续严格递增钟，两个事件在 $S$ 前出现当且仅当 $\theta(S)\ge t_2$，出现时 $s_j=\theta^{-1}(t_j)$。一个统一充分端点条件为 $\theta(S)\ge4\eta/\nu_{\min}$。（29.125）给 $\theta(S_*)\ge cS_*$；在相应 hit 时刻使用原点与两点增量不等式，得到（29.126）。绝对连续且几乎处处 $\theta'\ge c$ 是（29.125）的充分条件。仅 $\theta(s)\ge cs$ 已足够给总期限，但不能替代两点增量条件来给事件间隔界；允许任意快钟，所以没有统一正的外部下时间界。取得在第二 hit 停止，不使用超过 $T_c$ 的 PDE 演化。

在 $[0,\infty)$ 上若 $L=\lim_{s\to\infty}\theta(s)<\infty$，严格增加使有限时刻不达 $L$，故有限时刻到达第 $j$ 事件恰需 $t_j<L$；$L=\infty$ 时两个内部 hit 均最终可达。仅连续严格增加不足以保证最终取得：取 $L=\eta/(3\nu_{\max})$、$\theta(s)=L(1-e^{-s})$，则始终 $\theta(s)<L<t_1$。即使只许无界钟仍无统一期限：给任何 $D>0$，$\theta(s)=\eta s/(3\nu_{\max}D)$ 无界严格递增，却有 $\theta(D)=\eta/(3\nu_{\max})<t_1$。这些反例在同一个固定准备轨迹上就成立。

以上期限专属于两个精确阈值事件及真实可用的同时事件接口。任意有限个点查询不自动构成精确连续事件检测；检测器精度、带宽、延迟以及测量无扰动／等价轨迹须有各自假设。数值相同的迟时 $r$ 读数也不证明初始分支。定理29.4允许已经取得的偏离阈值记录，真实第二位置可达 $19\eta/8>2\eta$；本定理不把 $S_*$ 自动赋给这种记录或检测延迟。应用相同期限必须另给它们实际取得的证书，或另证更大目标及延迟的时域界，而不凭空指定取得算法。$\square$

**定理 29.6（相容竖直参数段上的三次有限差分）。** 固定 $m_0\ne0$，取 $d_0>0$ 使
$$
I=\{(m_0,k):k_0-d_0\le k\le k_0+d_0\}\subset U,\qquad k_0-d_0>0.
\tag{29.128}
$$
这里 $\nu(k)=|\alpha|/\sqrt k,\beta(k)=m_0\nu(k)$。令
$$
M_4=\sup_{(m_0,k)\in I,0\le r\le r_*}|\partial_k\partial_r^4g(m_0,k,r)|<\infty.
\tag{29.129}
$$
取 $\eta$ 满足（29.123），且 $2\eta\le r_*$；$M_4>0$ 时再要求 $\eta\le|m_0|/(10M_4)$，$M_4=0$ 时不加此限制。则对任意段内 $k,k'$，
$$
Q_\eta(k)=(g_{m_0,k}(\eta),g_{m_0,k}(2\eta)),\qquad
\frac{|m_0|}{15}\eta^3|k-k'|
 \le\|Q_\eta(k)-Q_\eta(k')\|_\infty
 \le\frac{|m_0|}{5}\eta^3|k-k'|.
\tag{29.130}
$$

证明。使用引理28.4的同一个参数微分积分余项，$F_k=0,G_k=-m_0/10$ 给
$$
\left|\partial_kg(m_0,k,r)+\frac{m_0}{60}r^3\right|
 \le\frac{M_4}{24}r^4.
\tag{29.131}
$$
对 $0<r\le2\eta$，附加小性使误差至多 $|m_0|r^3/120$，所以导数恒具有 $-\operatorname{sign}(m_0)$ 的符号，且
$$
\frac{|m_0|}{120}r^3\le|\partial_kg(m_0,k,r)|\le\frac{|m_0|}{40}r^3.
\tag{29.132}
$$
沿完整 $k$ 线段积分，固定符号排除抵消；第二输出在 $r=2\eta$ 给下界 $8/120=1/15$，两输出的最大上界为 $8/40=1/5$，得到真正有限差分（29.130）。几何包含 $I\subset U$ 本身不证明档案相容；下项对实际完整实现另加明确条件。$\square$

**定理 29.7（保留时间戳及全部已获 $r$ 迹的受限两点下界）。** 使用定理29.6的参数段和阈值。实验允许两个精确 $r$ 阈值 $\eta,2\eta$、它们的同时 $z$ 读数各有绝对误差至多 $\epsilon$，并保留所有校准、初点、准备族、局部先验、开始事件、取得历史和时间戳。可额外把 $m=m_0$ 精确告诉观察者。基础钟类取全部零点为零的连续严格递增钟；任何更强钟限制仍作为旧约束保留，并须通过下述完整端点条件。先声明两个 $z$ 坐标允许完整的 sup 范数误差球 $\{e:\|e\|_\infty\le\epsilon\}$；若实际联合噪声集更小，则以下两条构造误差向量必须分别被该集合允许。给 $\epsilon>0$，令
$$
d=\min\left\{d_0,\frac{5\epsilon}{|m_0|\eta^3}\right\},\qquad
k_-=k_0-d,\quad k_+=k_0+d,\qquad
\widetilde Z=\tfrac12(Q_\eta(k_+)+Q_\eta(k_-)).
\tag{29.133}
$$
对于所考察的固定完整旧档案，假设存在两个完整端点见证：参数为 $k_-,k_+$ 的实际 PDE、下面的各自单一钟、所构造噪声及所有辅助量，分别满足每条旧约束与合法取得关系，并给同一完整观察结果。则该受限实验的每个估计器，在这两份允许实现之一的绝对 $k$ 误差至少为 $d$；同样的界适用于 $(m,k)$ Euclidean 误差。以 $k_{\max}=k_0+d_0$ 计，物理坐标的最坏误差至少分别为
$$
\frac{|\alpha|}{2k_{\max}^{3/2}}d\quad\text{（黏性）},\qquad
\frac{|m_0\alpha|}{2k_{\max}^{3/2}}d\quad\text{（隐藏幅度）}.
\tag{29.134}
$$

证明。（29.130）给 $\|Q_\eta(k_+)-Q_\eta(k_-)\|_\infty\le2\epsilon$，故两个端点的误差向量 $e_\pm=\widetilde Z-Q_\eta(k_\pm)$ 都有 sup 范数至多 $\epsilon$。完整误差球允许这两个向量；若只给相关联合噪声限制，必须检查 $e_\pm$ 连同其它误差的实际联合归属，不能仅从逐坐标界推断允许。每个端点均是一条不同参数的真实光滑 PDE 轨迹，每份实现内部的两记录来自同一轨迹。

为保持外部时间戳，固定任意 $S>0$，对段内各参数取定理28.2的真实逆时间并令
$$
\theta_k(s)=t_k(\eta s/S)\quad(0\le s\le2S),\qquad
r_k(\theta_k(s))=\eta s/S.
\tag{29.135}
$$
这是连续严格递增、零点为零的钟，其内部像留在（29.123）的取得区间内。两次事件在全部候选中都有相同外部时间戳 $S,2S$；若取得时实际保留了整条 $r$ 监测迹，第二式也使这整条迹一致。需要时可在 $2S$ 后连续严格增加地延长钟，但延长部分的 PDE 读出和旧约束仍须有自身合法域。该钟是构造允许世界的见证，不是要求观察者预知隐藏参数的算法；每个世界用一个钟贯穿两事件，两个世界可以有不同允许钟。

基本档案只含上述共同校准、初始端口值、准备族／局部先验、开始事件及这些取得记录，并且准备标签没有泄露 $\beta,\nu$ 时，这两份完整见证确实相容：$x(0)=\alpha/2,y(0)=0$ 相同，阈值、时戳与 $r$ 迹由构造相同，$z$ 读数由中点噪声相同，准备和分支由实际解保证。对更丰富的档案，定理假设要求这些同一完整见证同时满足全部旧关系；旧钟校准、其它传感器、早先 $z$ 记录或准备元数据若排除任一端点，下界就不能用于该档案，不能删除这些信息来保留下界。尤其定理29.5用于充分取得的下增量率／期限限制不自动被（29.135）满足；若实验强制这些额外钟条件，须另外核对这两个钟在该固定合同下的可接受性。

估计器在同一完整观察结果上输出 $a$，三角不等式给
$$
2d=|k_+-k_-|\le|a-k_+|+|a-k_-|.
\tag{29.136}
$$
至少一项不小于 $d$。在以上限定的有界对抗噪声实验中因此有
$$
\text{minimax 绝对 }k\text{ 误差}\ \ge
\min\left\{d_0,\frac{5\epsilon}{|m_0|\eta^3}\right\}.
\tag{29.137}
$$
随机估计器在相同数据上有相同输出律，对三角不等式取期望也给最坏期望绝对误差的相同下界。这里无噪声独立性或随机分布前提。$\epsilon=0$ 时取 $d=0$，下界为零。

沿该段 $|\nu'(k)|=|\alpha|/(2k^{3/2})\ge|\alpha|/(2k_{\max}^{3/2})$ 且符号固定，端点差至少 $|\alpha|d/k_{\max}^{3/2}$。对物理参数的输出再次用两点三角不等式，取端点差的一半，即得（29.134）；$\beta=m_0\nu$ 给幅度常数。因此若所要求的最坏 $k$ 误差 $\delta<d_0$，在上述端点相容的噪声级别必须满足
$$
\epsilon\le\frac{|m_0|\delta}{5}\eta^3.
\tag{29.138}
$$

量词上，对给定 $(\eta,\epsilon)$，只要求（29.133）的两个端点连同钟、误差与旧记录的完整见证成立；要对每个噪声级别统一宣称（29.137），就须对全部相应 $d$ 验证这一条件，例如有一整段同时符合固定旧档案的完整见证族，并对每级中点误差保有联合允许性。仅 $I\subset U$ 或各条记录分别可拟合都不足。已知精确原始 $r$ 是允许的子实验，所以该下界与（29.117）在 $\epsilon_r=0$ 时的 $\eta^{-3}$ 量级相配，均在先验半径处饱和。

两个内部事件的间隔由（29.124）上下夹在常数乘 $\eta$ 之间，而剩余 $k$ 参数的输出分离仅为三次阶。这不是外部等待时间下界，因为（29.135）保留相同外部时刻。此匹配结论只针对声明的局部两端口、初始阈值、允许钟和联合噪声实验，不覆盖其它传感器、额外已获信息、任意后期时间、不同准备或更强先验，也不给普遍最优传感器数。方法是标准误差球重叠的两点估计论证；这里的具体桥梁是实际 PDE 系数给出的有限差分、保留时戳与 $r$ 迹的显式钟，以及完整档案的同时可实现条件。$\square$

## 29.99 追加锚

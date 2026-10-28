# FIB-native stopped eight-coordinate obstruction

This volume gives one ordinary proof for the stopped eight-coordinate obstruction and its quantitative positive-width gap. The proof concerns the original two-request class and a separately selected marked target law. The unchanged nonatomic targets remain part of the carrier and are not replaced by the marked laws.

## 1. Source, carrier, and resource class

The arithmetic source is

$$
X=\{(r,g): r\text{ is prime},\;g\in\mathbb Z,\;\lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},
\qquad N(r,g)=1+F_rg,
$$

where $F_0=0$, $F_1=1$, and $F_{k+2}=F_{k+1}+F_k$. Let $p_i$ be the $i$-th prime and put $q_i=[p_i\mid N(r,g)]$. The first absent coordinate is $n=\min\{i:q_i=0\}$. Every source integer has finitely many prime divisors, so this first absence is finite.

For every $j\ge1$, let $B_j$ and $P_j$ each be a Borel copy of $(0,1)$. The full carrier is their Borel disjoint union,

$$
\Omega=\left(\bigsqcup_{j\ge1}B_j\right)\sqcup\left(\bigsqcup_{j\ge1}P_j\right).
$$

The unchanged consumer returns unknown on each $B_j$ and proposes $j$ on each $P_j$, without making prime requests. Fix an amplitude sequence $1\ge a_1\ge a_2\ge\cdots>0$ with $a_n\to0$. The separately selected marked target at a first zero $n$ is

$$
\mu_n=(1-a_n)\,\delta_{\theta_0}+a_n\,\delta_{\theta_n},
\qquad
\theta_j=(B_1,1/(j+2)),\qquad j\ge0.
$$

For an acquisition $A$, define its uniform marked-target error by

$$
e_a(A)=\sup_{x\in X}\operatorname{TV}\bigl(\mathcal L(A(x)),\mu_{n(x)}\bigr).
$$

At a positive closed cap $e$, define the finite active horizon

$$
L_a(e)=\max\bigl(\{n:a_n>e\}\cup\{0\}\bigr).
$$

Thus an amplitude tied at $a_n=e$ is inactive. Accuracy in this volume is only accuracy to these separately selected marked laws. The original targets on the nonatomic blocks are still present; they have densities on their blocks, whereas each displayed marked law is atomic, so no assertion about their accuracy is transferred here.

The resource class has one source-independent random seed, zero advice, sourcewise almost-sure finite handoff, and at most two actual requests. An $N2$ rule must preselect its whole schedule before any reply and obtain all replies in that schedule; arbitrary addresses, repeated addresses, and ignored replies are allowed, with every actual request counted. An $O2$ schedule preselects an increasing schedule and every counterfactual output before any reply, stops at the first queried zero, and stops by exhaustion if no queried zero occurs. The first and second addresses of an $O2$ schedule are therefore not chosen from replies.

For $i<j$, write

$$
O(i,j;u,v,z)
$$

for the complete stopped table that outputs $u$ on the first queried zero, $v$ on the reply pattern $10$, and $z$ on $11$. Its counted $N2$ completion has outputs $(u,u,v,z)$ on the four reply patterns $00,01,10,11$. All counterfactual cells use the same schedule mass; no cell is assigned an independent probability budget.

The source existence and exact stopped-prefix transport used below are the supplied premises DEV297.1--297.4 and DEV309.1--309.3 at fixed source commit `07dfbdacb577f1cb1ebd6b6048ee3efa4c75285d`, file `docs/develop/theory/KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md`, sections 297, 300, 305, and 309. The nested premises named there (including 109.1, 110.2, 280.1, and 280.3) are credited premises rather than reproved claims in this volume.

## 2. The complete eight-coordinate table system

Consider one normalized allocation of whole deterministic stopped tables on coordinates $1,\ldots,8$ and labels $0,\ldots,8$. For a word $w\in\{0,1\}^8$ with first zero $n$, let $p_w(\ell)$ be the probability of output label $\ell$, put

$$
c_n(w)=p_w(n),
\qquad D_n(w)=1-p_w(0)-p_w(n).
$$

At a closed cap $e$, every nonpositive word has the three independent requirements

$$
p_w(0)\ge 1-b_n-e,
\qquad c_n(w)\ge b_n-e,
\qquad D_n(w)\le e.
$$

The positive word $+=11111111$ has the independent requirement $p_+(0)\ge1-e$. These are imposed for every original $A$, $C$, and $P$ row, including words with several later zeros, negative correct demands, arbitrary labels, and rows whose eventual score coefficient is zero. Constants, singleton schedules, repetitions, and ignored replies remain in the same system. Let $u_n$ denote the sole-zero word with its only zero at $n$.

## 3. The complete stopped score certificate

For a nonpositive scored word of first zero $n$, define

$$
g(w,\ell)=C_w[\ell=n]+P_w[\ell\in\{0,n\}],
$$

and define $g(+,\ell)=16[\ell=0]$. In a stopped cell, the rewards are summed over all words in that cell and then maximized over every label $0,\ldots,8$; an outside label has reward zero. The $A$ coefficients are all zero. The complete scored rows are:

| class | word : weight |
| --- | --- |
| $P$ | `00110000:1`, `00110010:3`, `01001010:3`, `01010001:3`, `01010010:2`, `01010100:1`, `01011001:3`, `01100001:1`, `01100010:1`, `01100100:4`, `01101000:3`, `10001000:3`, `10001001:1`, `10001010:1`, `10010010:3`, `10010100:3`, `10011000:1`, `10100001:6`, `10101000:1`, `11000100:4` |
| $C$ | `10110000:4`, `11000011:5`, `11001101:3`, `11010000:7`, `11011110:1`, `11100000:12`, `11100001:4`, `11101000:4`, `11110000:8`, `11110101:8`, `11110110:4`, `11111000:16`, `11111011:4`, `11111100:16`, `11111110:16` |
| $T$ | `11111111:16` |

For reference, the first stopped-cell reward vectors, with entries in label order $0,1,\ldots,8$, are

| first address | reward vector |
| ---: | --- |
| 1 | $(25,25,0,0,0,0,0,0,0)$ |
| 2 | $(23,4,23,0,0,0,0,0,0)$ |
| 3 | $(28,12,12,20,0,0,0,0,0)$ |
| 4 | $(28,12,12,12,20,0,0,0,0)$ |
| 5 | $(32,16,16,16,16,20,0,0,0)$ |
| 6 | $(36,20,20,12,20,8,20,0,0)$ |
| 7 | $(35,16,19,14,20,16,16,16,0)$ |
| 8 | $(34,18,16,12,16,12,16,16,16)$ |

The complete maxima and all argmax labels for every distinct pair are as follows. Each row lists the maxima on cells $0,10,11$, followed by the argmax set in each cell.

| pair | maxima | labels on $0$ | labels on $10$ | labels on $11$ |
| --- | --- | --- | --- | --- |
| $(1,2)$ | $(25,23,20)$ | $\{0,1\}$ | $\{2\}$ | $\{0,3,4,5,6\}$ |
| $(1,3)$ | $(25,20,23)$ | $\{0,1\}$ | $\{3\}$ | $\{0\}$ |
| $(1,4)$ | $(25,20,23)$ | $\{0,1\}$ | $\{4\}$ | $\{0\}$ |
| $(1,5)$ | $(25,20,23)$ | $\{0,1\}$ | $\{5\}$ | $\{0\}$ |
| $(1,6)$ | $(25,20,23)$ | $\{0,1\}$ | $\{2,4,6\}$ | $\{0\}$ |
| $(1,7)$ | $(25,20,20)$ | $\{0,1\}$ | $\{4\}$ | $\{0\}$ |
| $(1,8)$ | $(25,16,23)$ | $\{0,1\}$ | $\{0,2,4,6,7,8\}$ | $\{0\}$ |
| $(2,3)$ | $(23,20,25)$ | $\{0,2\}$ | $\{3\}$ | $\{0\}$ |
| $(2,4)$ | $(23,20,25)$ | $\{0,2\}$ | $\{4\}$ | $\{0\}$ |
| $(2,5)$ | $(23,20,25)$ | $\{0,2\}$ | $\{5\}$ | $\{0\}$ |
| $(2,6)$ | $(23,20,25)$ | $\{0,2\}$ | $\{4,6\}$ | $\{0\}$ |
| $(2,7)$ | $(23,20,22)$ | $\{0,2\}$ | $\{4\}$ | $\{0\}$ |
| $(2,8)$ | $(23,18,23)$ | $\{0,2\}$ | $\{0\}$ | $\{0\}$ |
| $(3,4)$ | $(28,20,20)$ | $\{0\}$ | $\{4\}$ | $\{0,5,6\}$ |
| $(3,5)$ | $(28,20,20)$ | $\{0\}$ | $\{5\}$ | $\{0,6\}$ |
| $(3,6)$ | $(28,20,20)$ | $\{0\}$ | $\{4,6\}$ | $\{0\}$ |
| $(3,7)$ | $(28,20,20)$ | $\{0\}$ | $\{4\}$ | $\{0\}$ |
| $(3,8)$ | $(28,16,23)$ | $\{0\}$ | $\{4,6,7,8\}$ | $\{0\}$ |
| $(4,5)$ | $(28,20,20)$ | $\{0\}$ | $\{5\}$ | $\{0,6\}$ |
| $(4,6)$ | $(28,20,20)$ | $\{0\}$ | $\{6\}$ | $\{0\}$ |
| $(4,7)$ | $(28,16,24)$ | $\{0\}$ | $\{5,6,7\}$ | $\{0\}$ |
| $(4,8)$ | $(28,16,22)$ | $\{0\}$ | $\{6,7,8\}$ | $\{0\}$ |
| $(5,6)$ | $(32,20,16)$ | $\{0\}$ | $\{6\}$ | $\{0,7,8\}$ |
| $(5,7)$ | $(32,16,20)$ | $\{0\}$ | $\{6,7\}$ | $\{0\}$ |
| $(5,8)$ | $(32,16,20)$ | $\{0\}$ | $\{6,7,8\}$ | $\{0\}$ |
| $(6,7)$ | $(36,16,16)$ | $\{0\}$ | $\{7\}$ | $\{0,8\}$ |
| $(6,8)$ | $(36,16,16)$ | $\{0\}$ | $\{7,8\}$ | $\{0\}$ |
| $(7,8)$ | $(35,16,16)$ | $\{0\}$ | $\{8\}$ | $\{0\}$ |

The seven pairs with total stopped score below $68$ have upper bounds

$$
(1,7),(1,8),(2,7),(2,8),(3,8),(4,8),(7,8)\quad\mapsto\quad65,64,65,64,67,66,67.
$$

The remaining twenty-one pairs have total $68$. A constant table has score at most $64$. A singleton at coordinate $i$ has zero-label rewards on the $w_i=1$ cell

$$
(39,41,36,36,32,28,29,30)_i,
$$

and every nonzero label has reward at most $25$; the $w_i=0$ cell is also zero-maximizing by the first-cell vectors. Thus every singleton and repetition has score at most $64$, and reversal gives no new increasing stopped partition. The complete support of score $68$ is therefore the twenty-one displayed pairs with their displayed label choices. The anchor

$$
R=O(1,2;1,2,0)
$$

has score $68$. The $P$ weights total $48$, the $C$ weights total $112$, the positive row contributes $16$, and the score vector for the correct classes is

$$
\beta=(0,4,16,20,20,20,16,16),\qquad K=176.
$$

All scores are integers, so every nonmaximizing table has score at most $67$. Earlier unqueried outputs, including labels $2,4,6$ in the $(1,6)$ $10$-cell and labels $5,6,7$ in the $(4,7)$ $10$-cell, are retained by the argmax table; no queried-label restriction has been imposed.

## 4. Score debt and the first paid replacement

Put

$$
S=b_3+b_4+b_5+b_6+b_7+b_8,
\qquad
s=1+44e-b_2-4b_3-5b_4-5b_5-5b_6-4b_7-4b_8.
$$

For one feasible allocation, the demanded score is

$$
\begin{aligned}
&48(1-e)+16(1-e)+4(b_2-e)+16(b_3-e)\\
&\qquad+20(b_4-e)+20(b_5-e)+20(b_6-e)+16(b_7-e)+16(b_8-e)=68-4s.
\end{aligned}
$$

Writing $E_r$ for each scored row event and $d_r$ for its demand, the exact score-debt identity is

$$
4s=\sum_D\lambda_D\bigl(68-\operatorname{score}(D)\bigr)+\sum_r Z_6(r)\bigl(p(E_r)-d_r\bigr).
$$

Every term is nonnegative: the first by the complete score certificate and the second by the row constraints, with positive integer coefficients. Hence $s\ge0$. Since every table below $68$ loses at least one score unit, their total mass is at most $\eta=4s$; each scored row slack is at most $\eta$ as well.

Replace every sub-$68$ table by the whole table $R$, preserving its complete counterfactual cells. The resulting normalized allocation $K_0$ has

$$
\varepsilon_0=2\eta.
$$

Every scored correct probability, scored union deficit, and positive nonbase mass is within $\varepsilon_0$ of its demand; every unscored correct probability is at least $b_n-e-\varepsilon_0$, and every unscored union deficit is at most $e+\varepsilon_0$. These replacements are proof allocations and need not remain cap-feasible; their changes are paid by the displayed error budget.

## 5. Four schedule charges and three output charges

In $K_0$, the following four differences are the masses of the indicated schedules:

$$
\begin{aligned}
D_1(01100001)-D_1(01100010)&=\operatorname{mass}(3,7),\\
D_1(01010001)-D_1(01010010)&=\operatorname{mass}(4,7),\\
D_2(10001000)-D_2(10001010)&=\operatorname{mass}(5,7),\\
D_2(10001000)-D_2(10001001)&=\operatorname{mass}(5,8).
\end{aligned}
$$

All eight words are scored $P$ rows. The first two comparisons have first zero at $1$ with $w_2=1$; the latter two have first zero at $2$. In each case every other stopped cell agrees or is already stopped, while the displayed second cell changes from a nonzero label to exhaustion label $0$. This remains true for every allowed counterfactual label and earlier unqueried output. Each mass is at most $2\varepsilon_0$. Replace all four schedule groups by $R$ and set

$$
\varepsilon_1=9\varepsilon_0.
$$

Let $u_2=10111111$, $u_4=11101111$, and $u_7=11111101$. In $K_1$ the complete support gives

$$
\begin{aligned}
p_{10110000}(2)-p_{u_2}(2)&=\operatorname{mass}\{(1,6):\text{ second output }2\},\\
p_{11100000}(4)-p_{u_4}(4)&=\operatorname{mass}\{(1,6),(2,6),(3,6):\text{ second output }4\},\\
p_{11111100}(7)-p_{u_7}(7)&=\operatorname{mass}\{(6,8):\text{ second output }7\}.
\end{aligned}
$$

The shared terms are, respectively, the prefix second cell and the first outputs from schedules beginning at $2$; prefix exhaustion $4$, both head-to-$4$ second cells and the $(3,4)$ second cell; and the $(6,7)$ second cell together with exhaustion $7$ on $(5,6)$. The remaining contributions vanish or agree. The first word in each difference is a scored $C$ row, while its sole-zero row supplies the lower bound. Hence each nonnegative group has mass at most $2\varepsilon_1$. Replace their union by $R$ and put

$$
\varepsilon_2=7\varepsilon_1=126\eta.
$$

Thus labels $2,4,7$ were allowed by the initial complete catalog and removed only through explicit paid comparisons.

## 6. Canonical support, head symmetry, and exact word identities

After these replacements the support has the following form. The prefix $(1,2)$ has first output $0$ or $1$, second output $2$, and exhaustion in $\{0,3,4,5,6\}$. For $h=1,2$ and $j=3,4,5,6$, schedule $(h,j)$ has first output $0$ or $h$, second output $j$, and exhaustion $0$. The remaining schedules are

$$
(3,4),(3,5),(3,6),(4,5),(4,6),(5,6),(6,7),(6,8),
$$

with first output $0$, second output the second queried address, and exhaustion sets

$$
\{0,5,6\},\{0,6\},\{0\},\{0,6\},\{0\},\{0,7,8\},\{0,8\},\{0\}.
$$

Let $t_j^{(h)}$ be the mass on $(h,j)$ and $v_j=t_j^{(2)}-t_j^{(1)}$ for $j=3,4,5,6$. The four scored differences

$$
\begin{aligned}
(01001010,10001010)&:v_3+v_4+v_6,\\
(01010010,10010010)&:v_3+v_5+v_6,\\
(01010100,10010100)&:v_3+v_5,\\
(01101000,10101000)&:v_4+v_6
\end{aligned}
$$

have absolute value at most $2\varepsilon_2$. Subtraction gives

$$
|v_6|,|v_3|\le4\varepsilon_2,
\qquad |v_4|,|v_5|\le6\varepsilon_2,
\qquad \sum_{j=3}^6|v_j|\le20\varepsilon_2.
$$

Average the two head masses at each $j$ and set both first outputs to $0$. Late correct stocks and the positive nonbase mass are preserved. The change in every needed head union deficit is at most $10\varepsilon_2$, and head symmetry identifies the relevant first-zero-$1$ and first-zero-$2$ deficits. Therefore, with

$$
\varepsilon=11\varepsilon_2=1386\eta,
$$

all late correct stocks differ from $b_n-e$ by at most $\varepsilon$, and the positive nonbase mass differs from $e$ by at most $\varepsilon$. The relevant scored union deficits on first-zero-$2$ words and first-zero-$1$ words with $w_2=1$ differ from $e$ by at most $\varepsilon$; every first-zero-$2$ union deficit, including an unscored one, is at most $e+\varepsilon$. No two-sided estimate for an unscored deficit is asserted, and no unchanged-deficit assertion for first-zero-$1$ words with $w_2=0$ is used.

Let $T$ be the total nonprefix schedule mass and $h_+$ the positive nonbase mass. Every nonprefix second cell contributes its schedule mass once to the six late correct stocks, and every nonzero exhaustion contributes once more to that stock sum and once to $h_+$. Hence, for this one allocation,

$$
\sum_{n=3}^8c_n=T+h_+.
$$

Write the masses of $(1,3),(1,4),(1,5),(1,6)$ (after symmetrization, equal to their $(2,j)$ partners) as $A,B,C_h,D_h$, and write the masses of $(3,4),(3,5),(3,6),(4,5),(4,6),(5,6),(6,7),(6,8)$ as $E,F,G,H,I,J,K,M$. Let $E_+,F_+,H_+,J_+,K_+$ denote their nonzero exhaustion masses. For a first-zero-$2$ suffix $(s,t,u,v,z,b)=(w_3,w_4,w_5,w_6,w_7,w_8)$, the actual union deficit is

$$
\begin{aligned}
D_2(w)={}&A(1-s)+B(1-t)+C_h(1-u)+D_h(1-v)\\
&+Es(1-t)+E_+st+Fs(1-u)+F_+su+Gs(1-v)\\
&+Ht(1-u)+H_+tu+It(1-v)\\
&+Ju(1-v)+J_+uv+Kv(1-z)+K_+vz+Mv(1-b).
\end{aligned}
$$

This is a table-by-table identity, including every exhaustion contribution. At the five relevant rows put

$$
\begin{aligned}
r_1&=D_2(10001000)=A+B+D_h+J,\\
r_2&=D_2(10010010)=A+C_h+D_h+H+I,\\
r_3&=D_2(10010100)=A+C_h+H+K+M,\\
r_5&=D_2(10100001)=B+C_h+D_h+E+F+G,\\
r_6&=D_2(10100100)=B+C_h+E+F+K+M.
\end{aligned}
$$

The first four are scored $P$ rows and $r_6=D_1(01100100)$ by head symmetry, so $|r_i-e|\le\varepsilon$ for $i=1,2,3,5,6$. Counting schedule masses gives

$$
T=G+r_1+r_2+r_6,
\qquad I-G=(r_2-r_3)-(r_5-r_6),
$$

and therefore $I\ge G-4\varepsilon$. The independent, generally unscored row $w_*=10001100$ has

$$
r_* =D_2(w_*)=A+B+J_++K+M\le e+\varepsilon.
$$

Since

$$
r_*-r_1=J_++G-(r_5-r_6)-J,
$$

we obtain $J\ge G+J_+-4\varepsilon\ge G-4\varepsilon$. The correct stock at label $6$ contains $G,I,J$ and only additional nonnegative stocks, so

$$
c_6\ge G+I+J\ge3G-8\varepsilon.
$$

## 7. The universal stopped inequality

The scored correct row at class $6$ gives $c_6\le b_6-e+\varepsilon$, hence

$$
3G\le b_6-e+9\varepsilon.
$$

The stock identity, the six lower bounds on $c_n$, and $h_+\le e+\varepsilon$ give

$$
T\ge S-7e-7\varepsilon.
$$

Using $T=G+r_1+r_2+r_6$ and the three upper bounds $r_i\le e+\varepsilon$ gives

$$
G\ge S-10e-10\varepsilon.
$$

Combining with the preceding upper bound on $3G$ yields

$$
3S-b_6-29e\le39\varepsilon=39\cdot1386\eta=216216s.
$$

Together with $s\ge0$, this proves the finite stopped theorem

$$
\boxed{s\ge0,\qquad 3S-b_6-29e\le216216s.}
$$

Equivalently, with $C=216216$,

$$
\boxed{
Cb_2+(4C+3)b_3+(5C+3)b_4+(5C+3)b_5+(5C+2)b_6+(4C+3)b_7+(4C+3)b_8
\le C+(44C+29)e.
}
$$

The constant is an exact certificate constant, deliberately coarse rather than optimized. When $s=0$, every charged mass is zero and the same proof directly gives $3S-b_6\le29e$; no division or limiting argument is used. The argument is for one common normalized allocation throughout. It uses no auxiliary hull, ordering of finite profiles, scalar renormalization, separate marginal optima, or counterfactual probability budgets.

## 8. Transport to every original $O2$ competitor

For an original $O2$ acquisition with positive closed cap $0<e\le1$, the supplied exact stopped class-feasibility and prefix transport gives one normalized complete stopped representative on a finite prefix. It includes arbitrary original addresses, arbitrary Borel outputs, the full carrier, all independent rows, and a common probability-one seed event from countability.

If its active horizon exceeds $8$, set higher finite replies to zero, project higher labels to zero, and contract the resulting constant observations. For a word whose first zero is already at most $8$, the target row is unchanged. On the positive word, the first higher zero projects to the base mark, so the positive row remains valid. If the active horizon is shorter than $8$, extend by ignored inputs. On each added first-zero fibre the old positive law is supported below that address and has exact error

$$
\max\{1-p_+(0),a_n\}\le e,
$$

including the endpoint $a_n=e$. Thus all added $A$, $C$, and $P$ rows remain valid, including negative correct demands and multiple-zero suffixes. These are representation operations on the stopped class; they do not preserve an arbitrary $N2$ law and do not grant an additional actual request.

For $e\ge1$, the expanded left side is at most $28C+17$ because every amplitude is at most one, while the right side is at least $45C+29$. For $0<e<1$, apply the finite theorem at the actual positive cap and decrease caps to the actual error; the expression is linear in the cap and the representatives may vary with the cap. A hypothetical zero-error competitor is covered by the positive-cap endpoint. Hence the universal inequality holds for every original $O2$ competitor at its actual error, with every positive nonincreasing vanishing continuation after coordinate $8$, whether or not it is summable.

## 9. Positive-width strict gap

Let

$$
0<\tau\le\frac1{24},\qquad 0<\delta\le\frac{\tau}{11},
$$

and set

$$
\begin{aligned}
&a_2=1-11\tau,\qquad (a_3,a_4,a_5,a_6,a_7)=(13,10,9,8,6)\tau,\\
&a_2\le a_1\le1-7\tau,\qquad a_8=5\tau+11\delta.
\end{aligned}
$$

The continuation satisfies $a_8\ge a_9\ge a_{10}\ge\cdots>0$ and $a_n\to0$, with no summability requirement. The order constraints hold on the whole parameter rectangle: $a_2\ge a_3$ follows from $\tau\le1/24$, and $a_8\le a_7$ follows from $\delta\le\tau/11$. The interval for $a_1$ is nonempty, and all displayed amplitudes are positive.

Put $r_0=5\tau+\delta$ and test a cap $e=r_0+t$. Then

$$
S=51\tau+11\delta,
\qquad s=44t,
\qquad 3S-a_6-29e=4\delta-29t.
$$

The universal inequality gives

$$
4\delta\le(29+44\cdot216216)t=9513533\,t.
$$

Therefore every original $O2$ competitor $O$ satisfies

$$
\boxed{e_a(O)\ge r_0+\frac{4\delta}{9513533}}.
$$

The gap is strictly positive throughout the declared family. It includes $\tau=1/24$, $\delta=\tau/11$ (where $a_8=a_7$), either endpoint of the $a_1$ interval, every permitted later-tail tie, and every positive vanishing nonsummable continuation. No condition on $a_9$ beyond the declared sequence order and vanishing is needed. At the cap $e=r_0$, if $a_9\le r_0$, including $a_9=r_0$, the active horizon is exactly eight: $a_8-r_0=10\delta>0$, while every amplitude from $a_9$ onward is at most $r_0$. The same lower bound applies without this extra condition on $a_9$. At $\delta=0$ the extra term vanishes and the boundary is the already attained DEV300 family with $a_8=5\tau$.

The old supplied lower bound from DEV305.3 remains valid for every original $N2$ competitor, namely $e_a(N)\ge r_0$. The new inequality is stronger only for $O2$ and does not establish whether an $N2$ rule attains $r_0$.

## 10. Credit and limits

The reused premises are the source, carrier, marked/nonatomic distinction, resource classes, complete independent event rows, finite-pattern actuality, and exact stopped transport from DEV297 and DEV309; the integer $Z6$ rows, support $68$, and the old $r_0$ lower bound from DEV305; the attained $\delta=0$ boundary from DEV300; the seven-active strips and cones from DEV306--307 and DEV312--313; and the residual/two-tail necessities from DEV304 and DEV310. Whole-vector support and complete convex-table methods from DEV303.3 and DEV314 are used as ordinary methods. No external priority or historical nonderivability claim is made.

The new content is the full stopped argmax refinement, including every cell maximum and argmax set, together with the charged use of sole-zero rows and the independent union row. It proves the universal finite inequality and transports it to every original $O2$ rule, yielding the strict positive-width gap above. The equality-face obstruction and its coarse quantitative extension are one result.

The following questions remain open: existence or nonexistence of an original $N2$ attainer at $r_0$, including the eight-active subfamily; the exact $O2$ optimum; an attaining $O2$ law at the displayed improved lower bound; the best improvement coefficient; a complete $N2/O2$ separator; interaction with longer-tail constraints and general amplitude families; and the unrestricted original comparison alternative. The extra unstopped $(3,8)$ cell has independent $00/01$ output freedom: its separate maxima $21$ and $8$ merge to $28$ in the stopped first cell, so the stopped support argument does not transfer to $N2$. No claim about physical efficiency, general neural networks, empirical machine learning, or overall completion follows.

The reference frame is the common attainable-vector problem for the original source, with one normalized complete stopped allocation carrying every word and counterfactual cell. The aesthetic choice of a symmetric common allocation is a bookkeeping guide only; the conclusion is fixed by the row inequalities and charged identities. The source and transport statements cited from DEV297 and DEV309 are verified ordinary premises supplied at the fixed source address above, while their nested source files are not independently certified here. This volume stops at the checked obstruction and records the remaining attainment and sharpness boundaries explicitly.

## 11. 追加锚（本行以下为增补区）

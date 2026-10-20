# FIB 自校准关系数学 VII

## 1. 完整目标与字面 JMMJM 历史

**定义 1.1（逐原子采集与实际纤维）。** Let $\mathcal W_3$ consist of
the triples $W=(P,g,\delta)$ with $P$ a strictly entrywise positive real
$2\times2$ matrix of rank one and trace one, $0\ne g\in\mathbb R[T]$ of
degree at most three, and $\delta\in\mathbb R$. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
$$

The original-clock reading is

$$
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.                 \tag{1.1}
$$

The initial reading counts. Each atom is immediately read on the single
unresettable, uncopyable trajectory. Eight total readings use precisely
clocks $0,\ldots,7$. There are no skipped readings, unread compound
actions, empty-action readings, clock renumberings or additional ports.
Actions, stops and complete-target answers may be arbitrary deterministic
functions of the entire actual history, without regularity assumptions.
All gain signs, lower degrees, sampled roots and repeated roots remain
legal. These are the conventions of [II, Definition 51.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).

Let $\mathcal F(H)$ retain every action and reading of a literal history.
For a known set $K\subseteq\mathcal F(H)$, use II, Definition 56.1:

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H)&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:
L_r(K\cap\mathcal F(H,E,z),(H,E,z)).
\end{aligned}                                                   \tag{1.2}
$$

The horizon is bounded by the remaining original clocks. Every child
uses the same fixed worlds and their shared ancestors. Responses to
unchosen actions are mathematical functions of those worlds; they are
not additional acquisitions. The negation of $L_r$ means recovery of
the whole known set within $r$ further readings, including early stops.

**定义 1.2（JMMJ 父历史及其实际第五 M 子历史）。** For arbitrary
$D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, set

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5),\\
H_J(Y)&=(H_J^-,J,Y),\qquad H_{JM}(Y,z)=(H_J(Y),M,z).
\end{aligned}                                                   \tag{1.3}
$$

These are exactly the $JMMJ$ histories of [V, Definition 5.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md),
with an actual fifth $M$ and its reading. The history parameter $D_0$
is not assumed to be the target's drift. Normalize readings and targets
by the bijection

$$
f=g/\lambda,\quad d=(\delta-D_0)/\lambda,\quad
\widehat Y=(Y-D_0)/\lambda,\quad \widehat z=(z-D_0)/\lambda.
                                                               \tag{1.4}
$$

Thus the six readings are $0,24,48,312/5,\widehat Y,\widehat z$.
This changes neither clocks nor sources nor target distinction nor
any $L_r$ predicate. It is valid for either sign of $\lambda$.

**定义 1.3（第五 M 后的正源坐标）。** The six cumulative matrices in
(1.3) are

$$
\begin{gathered}
I,\ J,\ L,\ J+L,\ C,\ Q,\qquad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\\
C=J(J+L)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix}
=I+2J+2L-C.
\end{gathered}                                                   \tag{1.5}
$$

For each fixed world put $\eta=(QP)_{22}>0$, $R=P/\eta$ and $F=\eta f$.
Since $Q^{-1}=\left(\begin{smallmatrix}-2&1\\3&-1\end{smallmatrix}\right)$,
the unique positive rank-one chart is

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(1-2x)y&1-2x\\(3x-1)y&3x-1\end{pmatrix},
\qquad \frac13<x<\frac12,\quad y>0.                           \tag{1.6}
$$

Indeed the $(2,2)$ entry of $QR$ is one, and its rank-one determinant
gives the $(1,1)$ entry $xy$. Multiplying by $Q^{-1}$ gives the displayed
$R$; its four entries are positive exactly on the stated strip. Conversely
this strip gives positive rank-one representatives, with
$P=R/\operatorname{tr}R$ and $f=(\operatorname{tr}R)F$.

Write $s=x+y$, $p=xy$. The traces against the six matrices in (1.5) are

$$
(T_0,T_1,T_2,T_3,T_4,T_5)
=(s+2x-2p-1,\ 1-x-s+3p,\ s-2p,\ 1-x+p,\ s-p,\ p+1).
                                                               \tag{1.7}
$$

Each is positive. Every world satisfies the entire set of equations

$$
F(i)T_i+d=(0,24,48,312/5,\widehat Y,\widehat z)_i
\quad(0\le i\le5).                                           \tag{1.8}
$$

The sixth-$J$ and sixth-$M$ traces are respectively $s,s+1$, obtained
by multiplying $QR$ by the individual atom. No ancestor equation is
discarded by this change of coordinates.

## 2. 同漂移的六、七双根层

**引理 2.1（JMMJM 固定漂移双末根注入性）。** In any normalized entire
history (1.8), at each fixed $d\in\mathbb R$ there is at most one complete
target with $f(6)=f(7)=0$.

Proof. In the trace-one normalization write

$$
f_i(T)=(T-6)(T-7)(a+b_iT),\qquad a=-d/42.                    \tag{2.1}
$$

The common $a$ follows from the initial reading. This factorization
includes every permitted lower degree and further root multiplicity.
If $a=0$, a nonzero gain has $b_i\ne0$. Clocks one, two and three then
give, for even a single target,

$$
\operatorname{tr}(JP)=\frac4{5b_i},\quad
\operatorname{tr}(LP)=\frac6{5b_i},\quad
\operatorname{tr}((J+L)P)=\frac{26}{15b_i}.
$$

The first two traces sum to $2/b_i$, contradicting the third. Hence
$a\ne0$.

If $b_1=b_2$, the common nonzero polynomial has at most one zero among
clocks $0,\ldots,5$, since six and seven are already distinct roots.
Every five of the six matrices in (1.5) span $\operatorname{Mat}_2(\mathbb R)$:
$I,J,L,C$ are a basis, $J+L$ replaces either missing $J$ or missing $L$,
and $Q=I+2J+2L-C$ replaces either missing $I$ or missing $C$.
For the basis assertion, the diagonal difference in
$a_0I+a_1J+a_2L+a_3C=0$ first gives $a_3=0$; the off-diagonal
difference gives $a_2=0$, and then $a_0=a_1=0$.
The shared readings at the nonzero samples therefore force $P_1=P_2$.

Suppose instead $A=b_1-b_2\ne0$, and put

$$
U=a(P_1-P_2),\qquad V=b_1P_1-b_2P_2,\qquad B=\operatorname{tr}(JV).
                                                               \tag{2.2}
$$

The six common readings, after division only by the nonzero integers
$(i-6)(i-7)$, say $\operatorname{tr}(A_i(U+iV))=0$.
Also $\operatorname{tr}U=0$ and $\operatorname{tr}V=A$.
The equations at one and two give
$\operatorname{tr}(JU)=-B$ and
$\operatorname{tr}(LU)=-2\operatorname{tr}(LV)$.
The equation at three then gives $\operatorname{tr}(LV)=-2B$.
The last two equations, using the expression for $Q$ in (1.5), give
$\operatorname{tr}(CV)=5A-4B$ and
$\operatorname{tr}(CU)=-20A+16B$. Solving these basis traces yields

$$
U=\begin{pmatrix}-20A+17B&4B\\-5B&20A-17B\end{pmatrix},\qquad
V=\begin{pmatrix}4A-5B&-A-2B\\A+3B&-3A+5B\end{pmatrix}.
                                                               \tag{2.3}
$$

Let $\rho=B/A$ and $\mu_i=b_i/a$. Since
$P_1=(V-\mu_2U)/A$ and $P_2=(V-\mu_1U)/A$, positivity gives

$$
\operatorname{tr}(JP_i)=\rho(1+\mu_{3-i})>0,\qquad
\operatorname{tr}(LP_i)=-2\rho(1+2\mu_{3-i})>0.                \tag{2.4}
$$

If $\rho=0$, the first inequality fails. If $\rho<0$, the two inequalities
require simultaneously $\mu_{3-i}<-1$ and $\mu_{3-i}>-1/2$.
Consequently

$$
\rho>0,\qquad -1<\mu_1,\mu_2<-1/2.                          \tag{2.5}
$$

The samples $f_i(1)$ and $f_i(2)$ have opposite signs. Their positive
trace factors and the actual readings force $24<d<48$.
Define the auxiliary quadratic
$\Phi(T)=\rho(1+\mu_1T)(1+\mu_2T)$. Equations (2.4), together with
$\operatorname{tr}((J+L)P_i)=-\rho(1+3\mu_{3-i})$, give

$$
\Phi(1)=\frac{24-d}{30a},\quad
\Phi(2)=-\frac{48-d}{40a},\quad
\Phi(3)=-\frac{312/5-d}{12a}.
$$

Quadratic interpolation at zero now gives

$$
\rho=3\Phi(1)-3\Phi(2)+\Phi(3)
=\frac{77d-672}{20d}>\frac{49}{20}>2.                         \tag{2.6}
$$

For either positive matrix $P_i$, eliminate $\mu_{3-i}$ between its
$(1,1)$ and $(1,2)$ entries in (2.3):

$$
(P_i)_{11}=\frac{17\rho-20}{4\rho}(P_i)_{12}
             +\frac{14\rho^2-7\rho-20}{4\rho}.                \tag{2.7}
$$

For $\rho>2$ the first coefficient is positive and the constant is
greater than one. The latter inequality is
$14\rho^2-11\rho-20>0$, since its value at two is $14$ and its
derivative is positive thereafter. Thus $(P_i)_{11}>1$, contradicting
strict positivity and trace one. This excludes unequal $b_i$ and
proves uniqueness. No gain sample or discriminant was divided out. ∎

## 3. 同和割线的有限有理正性证书

**定义 3.1（插值子式及其完整系数）。** For real variables $q,s,u$, define

$$
\begin{aligned}
Z&=2s+1,\\
A_0&=40(1-q)Z,& B_0&=28(1-q)s+8+q+9q^2-18u,\\
B_1&=(15q/2-5)s-2q-1-5q^2/2+5u,
&A_1&=B_1+4(3q-1)Z,\\
B_3&=9u-(1+7q/2)s+1-10q-9q^2/2,
&A_3&=3B_3+2(1-q)Z,\\
C_{ij}&=A_iB_j-A_jB_i\qquad(i,j\in\{0,1,3\}).
\end{aligned}                                                   \tag{3.1}
$$

In the following polynomials substitute

$$
s=q+2m,\qquad u=q(1-m)+2m-m^2+v,\qquad
G_1=C_{03},\quad G_2=-C_{01},\quad G_3=-C_{13}.                \tag{3.2}
$$

Let $B_{i,n}(X)=\binom niX^i(1-X)^{n-i}$, and set

$$
(a_1,b_1)=(0,1/4),\quad (a_2,b_2)=(1/4,2/3),\quad
(a_3,b_3)=(2/3,1),\qquad
(D_1,D_2,D_3)=(18432,497664,62208).
$$

The complete integer coefficient matrices $N^{(r,k)}$, with rows
$i=0,\ldots,4$, columns $j=0,\ldots,4$ and $k=0,1,2$, are as follows:

$$
\begin{aligned}
N^{(1,0)}&=\begin{pmatrix}
2826240&2430720&1986432&1508928&1021536\\
3204096&2753568&2254032&1722336&1183104\\
3549696&3041808&2485688&1899480&1309104\\
3836160&3270456&2658312&2019168&1380240\\
4043520&3421440&2755728&2067120&1384128
\end{pmatrix},\\
N^{(1,1)}&=\begin{pmatrix}
2875008&2477556&2030862&1550478&1059732\\
3256224&2803527&2301348&1766535&1223712\\
3604896&3094602&2535602&1946040&1351836\\
3894144&3325797&2710536&2067801&1424808\\
4104000&3479040&2809974&2117538&1430244
\end{pmatrix},\\
N^{(1,2)}&=\begin{pmatrix}
2924208&2524824&2075724&1592460&1098360\\
3308784&2853918&2349096&1811166&1264752\\
3660528&3147828&2585948&1993032&1395000\\
3952560&3381570&2763192&2116866&1469808\\
4164912&3537072&2864652&2168388&1476792
\end{pmatrix}.
\end{aligned}                                                   \tag{3.3}
$$

$$
\begin{aligned}
N^{(2,0)}&=\begin{pmatrix}
10424376&21164856&29233536&30748416&19562496\\
10900872&22453692&30863712&32022432&19556352\\
12007656&24514296&33381336&34273776&20591616\\
13975416&27603396&37069176&37811256&23003136\\
17000280&31943160&42175440&42909120&27091200
\end{pmatrix},\\
N^{(2,1)}&=\begin{pmatrix}
9936540&20598870&28578550&29993580&18696960\\
10384200&21855615&30173380&31228995&18648960\\
11463588&23885568&32657098&33443178&19643808\\
13405392&26945457&36312472&36944937&22016352\\
16405740&31257450&41387710&42008520&26066880
\end{pmatrix},\\
N^{(2,2)}&=\begin{pmatrix}
9446544&20030724&27921404&29236584&17829264\\
9865368&21255378&29480888&30433398&17739408\\
10917360&23254680&31930700&32610420&18693840\\
12833208&26285358&35553608&36076458&21027408\\
15809040&30569580&40597820&41105760&25040400
\end{pmatrix}.
\end{aligned}                                                   \tag{3.4}
$$

$$
\begin{aligned}
N^{(3,0)}&=\begin{pmatrix}
2472960&4184832&6751488&10448256&15621120\\
2600064&4415040&7134720&11043264&16495488\\
2766912&4701840&7594560&11738064&17496000\\
2979072&5053512&8142000&12546360&18639072\\
3246432&5482656&8792352&13486176&19945440
\end{pmatrix},\\
N^{(3,1)}&=\begin{pmatrix}
2446416&4148676&6704816&10390164&15550704\\
2572824&4377849&7086674&10983459&16423020\\
2738796&4663434&7544960&11676366&17421300\\
2949900&5013711&8090666&12482589&18561960\\
3216024&5441280&8739104&13420152&19865736
\end{pmatrix},\\
N^{(3,2)}&=\begin{pmatrix}
2420142&4112790&6658414&10332342&15480558\\
2545854&4340928&7038898&10923924&16350822\\
2710950&4625298&7495630&11614938&17346870\\
2920998&4974180&8039602&12419088&18485118\\
3185886&5400174&8686126&13354398&19786302
\end{pmatrix}.
\end{aligned}                                                   \tag{3.5}
$$

**引理 3.2（覆盖同和割线的三个严格正子式）。** On
$1/3\le m\le1/2$ and $0\le v\le1/144$, the substitutions (3.2) satisfy

$$
\begin{array}{c|c}
\text{interval for }q&\text{strictly positive polynomial}\\ \hline
[0,1/4]&C_{03}\\
[1/4,2/3]&-C_{01}\\
[2/3,1]&-C_{13}.
\end{array}                                                     \tag{3.6}
$$

Proof. The exact polynomial identities furnished by (3.1)–(3.5) are

$$
G_r\left(\frac13+\frac X6,\ a_r+(b_r-a_r)U,\ \frac V{144}\right)
=\frac1{D_r}\sum_{i,j=0}^4\sum_{k=0}^2
N^{(r,k)}_{ij}B_{i,4}(X)B_{j,4}(U)B_{k,2}(V).                 \tag{3.7}
$$

Here the argument order on the left is $(m,q,v)$ after (3.2).
For a direct coefficient specification of every entry, let
$c^{(r)}_{abc}$ be the coefficient of $X^aU^bV^c$ in that left side.
Expansion of the displayed quadratic factors gives degree at most
$(4,4,2)$, and the data (3.3)–(3.5) obey

$$
\frac{N^{(r,k)}_{ij}}{D_r}
=\sum_{a=0}^i\sum_{b=0}^j\sum_{c=0}^k
c^{(r)}_{abc}
\frac{\binom ia}{\binom4a}
\frac{\binom jb}{\binom4b}
\frac{\binom kc}{\binom2c}.                                  \tag{3.8}
$$

Thus all coefficients in (3.7) are specified by rational arithmetic
from (3.1), with no unspecified fitted coefficient. To verify the
conversion, expand the binomial theorem after factoring $X^a$ to obtain
$X^a=\sum_{i=a}^n\binom ia\binom na^{-1}B_{i,n}(X)$, and apply it in
each of the three variables. This gives exactly (3.8) and (3.7).
For example the least coefficients for $r=1,2,3$ are respectively

$$
\frac{1021536}{18432}=\frac{3547}{64},\qquad
\frac{9446544}{497664}=\frac{7289}{384},\qquad
\frac{2420142}{62208}=\frac{403357}{10368},
$$

all positive. Every integer in the nine matrices is positive. On the
unit cube the tensor Bernstein terms are nonnegative and sum to one.
Consequently (3.7) is strictly positive on that whole cube, proving
all three closed-box assertions. ∎

## 4. JMMJM 任意漂移二目标排除

**定理 4.1（每个完整实际第五 M 纤维都没有二目标 L2）。** For every
$D_0,Y,z\in\mathbb R$, $\lambda\ne0$ and two distinct complete targets
$W_1,W_2\in\mathcal F(H_{JM}(Y,z))$,

$$
\neg L_2(\{W_1,W_2\},H_{JM}(Y,z)).                           \tag{4.1}
$$

There is no drift, gain-ray or nonzero-sample promise on the pair.

Proof. Normalize by (1.4), and suppose a fixed pair has $L_2$. Both
sixth readings and all four chronological sixth/seventh terminal
readings must agree on that same pair: any discrepancy gives an
actually executable separating suffix of at most two atoms.

Apply the four-terminal calculation of [V, Theorem 7.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)
to the actual $Q$ in (1.5). Explicitly, for
$X=f(7)QP=\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$,
the terminal readings are

$$
r_{MM}=a+b+c+2e+d,\quad r_{MJ}=a+c+e+d,\quad
r_{JM}=a+b+e+d,\quad r_{JJ}=a+e+d.                            \tag{4.2}
$$

Their differences determine $b,c,e$. If $e\ne0$, rank one gives
$a=bc/e$ and then $d=r_{JJ}-a-e$. If $e=0$, strict positivity of
$QP$ forces $f(7)=0$ and $X=0$, and every terminal reading is $d$.
Hence the two targets have equal $d$ and equal $X$. If $X\ne0$,
$Q^{-1}X=f(7)P$ and trace one recover the same $P$ and $f(7)$.
The four shared ancestor readings at $0,1,2,3$, with positive trace
factors, then recover the same polynomial $f$. This contradicts
target distinction. Thus

$$
d_1=d_2=d,\qquad f_1(7)=f_2(7)=0.                           \tag{4.3}
$$

In chart (1.6), equality of both sixth readings gives

$$
F_1(6)=F_2(6)=c,\qquad c(s_1-s_2)=0.                        \tag{4.4}
$$

If $c=0$, both trace-one gains have roots six and seven and Lemma 2.1
gives identical complete targets. Suppose $c\ne0$. Then $s_1=s_2=s$.
If $x_1=x_2$, also $y_1=y_2$, giving the same source and, by the
four ancestor readings and common drift, the same gain. Therefore put

$$
\begin{gathered}
\Delta=x_1-x_2\ne0,\quad q=s-x_1-x_2,\quad
m=(x_1+x_2)/2,\quad v=\Delta^2/4,\quad
u=(T_{1,4}+T_{2,4})/2,\\
s=q+2m,\qquad u=q(1-m)+2m-m^2+v,\qquad
\frac13<m<\frac12,\quad 0<v<\frac1{144}.
\end{gathered}                                                   \tag{4.5}
$$

Here $T_{j,i}$ denotes world $j$'s trace at clock $i$. Direct subtraction
of (1.7), using $p_1-p_2=q\Delta$, gives

$$
\begin{aligned}
(T_{1,i}-T_{2,i})/\Delta&=\ell_i,\\
(\ell_0,\ldots,\ell_5)&=(2(1-q),3q-1,-2q,q-1,-q,q),\\
\overline T_i=(T_{1,i}+T_{2,i})/2
&=\left(2u-q-1,\ 1+\frac{3s+q}{2}-3u,\ 2u-s,\
1+\frac{s+q}{2}-u,\ u,\ s+1-u\right)_i.
\end{aligned}                                                   \tag{4.6}
$$

All $\overline T_i$ are positive. The common sixth sample and seventh
root allow the factorizations

$$
\frac{F_1(T)-F_2(T)}\Delta=(T-6)(T-7)(\alpha T+\beta),\qquad
\frac{F_1(T)+F_2(T)}2=(T-7)h(T),\quad \deg h\le2.             \tag{4.7}
$$

Subtracting the two actual equations (1.8) gives, at every $i=0,\ldots,5$,

$$
\ell_i h(i)+(i-6)(\alpha i+\beta)\overline T_i=0.             \tag{4.8}
$$

At least three of the $\ell_i$ are nonzero for every $q$. Thus
$\alpha=\beta=0$ would give three distinct zeros of $h$, making
$h=0$ and both gains zero. Hence $(\alpha,\beta)\ne(0,0)$.

If $q=0$, equal traces at $2,4,5$ force $F_1-F_2$ to vanish there;
it also vanishes at six and seven. If $q=1$, equal traces at zero
and three, together with six and seven, give four distinct zeros.
In either case the difference polynomial vanishes identically,
contradicting the preceding conclusion. Hence $q\ne0,1$.

If $q<0$ or $q>1$, the four signs of $\ell_0,\ell_1,\ell_2,\ell_3$
alternate. Put $h_i^*=(0,24,48,312/5)_i$. Since both positive trace
factors give the same actual reading,

$$
\operatorname{sgn}h(i)=-\operatorname{sgn}(h_i^*-d)
\quad(0\le i\le3).
$$

Equation (4.8) therefore requires
$\operatorname{sgn}(\alpha i+\beta)
=-\operatorname{sgn}(\ell_i)\operatorname{sgn}(h_i^*-d)$.
When none of these four readings equals $d$, the second sign sequence
has at most one change, because the four $h_i^*$ strictly increase.
Multiplying it by an alternating sequence leaves at least two sign
changes. A nonzero affine function cannot have those signs.
If $d=h_j^*$ for one index $j$, then $F_1(j)=F_2(j)=0$ and
$\alpha j+\beta=0$. Thus $\alpha\ne0$ and, at the other three indices,
both $\alpha i+\beta$ and $h_i^*-d$ have the threshold sign
$\operatorname{sgn}(i-j)$ up to a fixed sign. The displayed equality
would make all three remaining $\ell_i$ have the same sign, whereas
deleting one term of an alternating four-term sequence leaves both
signs. This is also impossible. Therefore

$$
0<q<1.                                                       \tag{4.9}
$$

It remains to impose all six equations (4.8) in this interval.
The equations at two, four and five determine the quadratic $qh$:

$$
\begin{aligned}
qh(2)&=-2(2\alpha+\beta)(2u-s),\\
qh(4)&=-2(4\alpha+\beta)u,\\
qh(5)&=(5\alpha+\beta)(s+1-u).
\end{aligned}                                                   \tag{4.10}
$$

Explicitly, for these three right sides $V_2,V_4,V_5$,

$$
qh(T)=\frac{(T-4)(T-5)}6V_2
       -\frac{(T-2)(T-5)}2V_4
       +\frac{(T-2)(T-4)}3V_5.                               \tag{4.11}
$$

Substitute (4.11) into the remaining equations. With the polynomials
of (3.1), their left sides multiplied by $q$ are exactly

$$
\begin{array}{c|c}
i&\ell_i(qh)(i)+q(i-6)(\alpha i+\beta)\overline T_i\\ \hline
0&2(A_0\alpha+B_0\beta)/3\\
1&A_1\alpha+B_1\beta\\
3&(A_3\alpha+B_3\beta)/3.
\end{array}                                                     \tag{4.12}
$$

This supplies an explicit interpolation identity for each row, with
only the integer denominators in (4.11). Since $(\alpha,\beta)\ne(0,0)$,
the three row vectors $(A_i,B_i)$ must have every two-by-two minor
zero. In particular $C_{01}=C_{03}=C_{13}=0$. But (4.5), (4.9)
put the same pair in one of the three boxes of Lemma 3.2, where one
of these minors is strictly nonzero. This contradiction excludes
$c\ne0$ and completes the proof.

The proof divided only by fixed nonzero integers, $\lambda\ne0$,
positive trace normalizations, $\Delta\ne0$, and $q\ne0$ after its
zero case. The terminal division by $e$ occurred only in its nonzero
case; Lemma 2.1 separately established all its divisors. No sampled
gain was presumed nonzero. Both signs, lower degrees, additional
sampled roots and repeated roots are included. The actual fourth
and fifth readings enter (4.8) at four and five; the gains and sources
remain the original fixed worlds throughout. ∎

## 5. 实际小子纤维的整族消费者

**定理 5.1（任意漂移、变第五响应的条件整族恢复）。** Fix $D_0,\lambda,Y$
as in (1.3). Let $K\subseteq\mathcal F(H_J(Y))$ be known, of arbitrary
cardinality and with arbitrary drifts. Suppose that every entire actual
fifth-$M$ response fiber

$$
K_z=K\cap\mathcal F(H_{JM}(Y,z))
$$

contains at most two distinct complete targets. Then one deterministic
strategy recovers every member of $K$ within three further readings,
hence within eight total readings.

The same total budget holds for a known $K\subseteq\mathcal F(H_J^-)$
if every entire actual fourth-$J$, fifth-$M$ response fiber has at most
two targets.

Proof. At $H_J(Y)$ execute fifth $M$ and read its actual $z$. A singleton
returns its complete target. For a pair, Theorem 4.1 guarantees a
separating suffix of length at most two. Choose the first word in the
fixed order $MM,MJ,JM,JJ$ whose sixth or seventh reading differs on
that whole retained pair. Execute its sixth atom and read; if it
separates, stop, otherwise execute and read its seventh atom. Return
the unique retained target matching the actual readings. The word
exists because equality of both sixth readings and all four terminal
readings would be precisely two-target $L_2$.

This defines one policy for every reachable $z$ of the same known
$K$, including infinitely many possible response values. Empty fibers
are unreachable. At $H_J^-$ first execute fourth $J$ and read $Y$,
then use the stated rule on that actual retained set. Each atom is
immediately read and the last possible clock is seven. The budgets
are $5+1+2=8$ and $4+1+1+2=8$. No drift promise is required. ∎

**推论 5.2（失败实际子纤维至少含三目标）。** For any known compatible
$K$ at $H_J(Y)$,

$$
L_3(K,H_J(Y))\ \Longrightarrow\
\exists z:\ L_2(K_z,H_{JM}(Y,z))\ \land\ |K_z|\ge3.          \tag{5.1}
$$

In particular, an $L_3$ set of exactly three targets at this $JMMJ$
parent must have constant fifth-$M$ response. An $L_4$ family at
$H_J^-$ must retain such an at-least-three-target $L_2$ child after
some actual fourth-$J$ and fifth-$M$ readings.

Proof. The recursion (1.2) supplies the actual losing child for fifth
$M$. It has at least two targets, and Theorem 4.1 excludes exactly
two. If the parent contains exactly three, that child is the whole
parent. At the preceding history first unfold (1.2) at fourth $J$,
retaining its actual $Y$, and apply the same assertion to that
child's actual fifth-$M$ fiber. These are necessary conditions only;
they do not supply a realization of a larger losing child. ∎

## 6. 另一字面 MMJM 历史的共同 b、d 整类应用

**定义 6.1（共同预测是已知候选承诺）。** Independently of (1.3), use
the literal parent and response functions of
[II, Definitions 69.1–69.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
H_4(Y)=(0,M,1,M,23/7,J,331/35,M,Y),\qquad
D=MJM^2=\begin{pmatrix}1&1\\2&3\end{pmatrix}.
                                                               \tag{6.1}
$$

For $\eta=(DP)_{22}>0$, $R=P/\eta$, $H=\eta g$, the coordinates are

$$
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},
\qquad 1/3<x<1/2,\quad y>0.                                 \tag{6.2}
$$

They belong to this $D$, not the $Q$ of (1.5). Let
$\mathcal F(Y;m,j)$ impose both fifth predictions, $m$ after $M$ and
$j$ after $J$, on the entire parent (6.1). Write
$\kappa=m-j$, $s=x+y$, $p=xy$, $v_6=H(6)$. The existing identities are

$$
\begin{gathered}
H(5)=\kappa,\qquad \delta=j-\kappa s,\\
a=\operatorname{read}(JJ)=\delta+v_6(p+1),\qquad
b=\operatorname{read}(JM)=a+v_6x,\\
c=\operatorname{read}(MJ)=a+v_6y,\qquad
d_6=\operatorname{read}(MM)=c+v_6(x+1).
\end{gathered}                                                   \tag{6.3}
$$

Words in (6.3) are chronological fifth/sixth choices, each atom
individually read. Fix known real constants $Y,m,j,b_0,d_0$ and define
the entire promised class

$$
\mathcal C=\{W\in\mathcal F(Y;m,j): b(W)=b_0,\ d_6(W)=d_0\},
\qquad \omega=d_0-b_0.                                      \tag{6.4}
$$

These constants describe known candidates. They are not readings
acquired on both branches of a single trajectory. The class has no
cardinality bound. All parent equations, including the same literal
$Y$, remain imposed. Within $\mathcal F(Y;m,j)$, $x,y$ determine the
complete target: (6.2) determines the source, (6.3) determines the
drift, and the positive parent trace factors at $0,1,2,3$ determine
the entire cubic-or-lower gain by interpolation, as in II, Definition 69.1.

**定理 6.2（共同 b、d 类的一条整族单射臂）。** If $\omega\ne0$, at
least one of $a,c$ is injective on all of $\mathcal C$, even if the
putative collision pairs are disjoint. One policy recovers every
complete target in this known class by original clock six, with
seven total readings. This nonzero-$\omega$ assertion allows
$\kappa=0$ as well as $\kappa\ne0$.

If $\omega=0$ and $\kappa\ne0$, the whole class is recovered by the
fixed continuation $J,J,J$, with eight total readings.

Proof. For $\omega\ne0$, apply the response-curve mechanism of
[II, Theorem 70.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
to the common-$b,d_6$ equations of II, Theorem 72.1. Its parameter
correspondence here is

$$
t=\frac1{y+1}\in(0,1),\quad \rho=\frac\kappa\omega,\quad
e=1-\rho,\quad K=\frac{b_0-j}\omega-\rho,\quad H(6)=\omega t.
                                                               \tag{6.5}
$$

Substitution in (6.3) gives exactly

$$
e x=K+\rho/t-t,\qquad
a=b_0-\omega tx,\qquad c=d_0-\omega t(x+1).                  \tag{6.6}
$$

For example $b_0-j=-\kappa(x+y)+\omega t(xy+x+1)$;
use $y=1/t-1$ and $t(xy+x)=x$ to obtain the first identity.
Thus this is the same curve equation as II, equation (70.2), with
its curve constant $k$ replaced by $K$ and with the additional
restriction $t<1$. Multiplication by either sign of $-\omega$ does
not change collisions. The following cases give its whole-class
consequence on this restricted curve.

If $\rho=1$, the equation is $K=t-1/t$, strictly increasing for
$t>0$, so the entire class has one value of $t$. Both remaining
responses in (6.6) are affine in $x$ with nonzero slope. They are
both injective, since equal $x,t$ give equal $x,y$ and complete targets.

Suppose $e\ne0$. A parameter $t$ uniquely fixes $x$ and $y$, hence
the complete target. Consequently different targets have different
$t$. The identities

$$
tx=\frac{\rho+Kt-t^2}{e},\qquad
t(x+1)=\frac{\rho+(K+e)t-t^2}{e}                              \tag{6.7}
$$

show that an $a$ collision at two distinct parameters requires
$t_1+t_2=K$, and a $c$ collision requires $t_3+t_4=K+e$.
No common endpoint between these pairs is assumed.
If $\rho>1$, the first collision would give
$x(t_1)=(t_2+\rho/t_1)/e<0$; the second would give
$x(t_3)+1=(t_4+\rho/t_3)/e<0$. Thus both arms are injective.
If $\rho<0$, then $e>1$, and a $c$ collision would instead give

$$
x(t_3)+1=\frac{t_4+\rho/t_3}{e}<\frac{t_4}{e}<1,
$$

contrary to $x>1/3$. Therefore $c$ is injective throughout this
case. This uses the actual $t<1$ restriction in (6.5).

It remains that $0\le\rho<1$, $e>0$. The function
$x(t)=(K+\rho/t-t)/e$ is strictly decreasing on $t>0$.
Its legal set $I=\{t\in(0,1):1/3<x(t)<1/2\}$ is an interval.
For $t_1<t_2$ in this interval,

$$
x(t_1)-x(t_2)
=\frac{t_2-t_1}{e}\left(1+\frac\rho{t_1t_2}\right)
\ge\frac{t_2-t_1}{e},\qquad t_2-t_1<e/6.                    \tag{6.8}
$$

If both kinds of collision existed, their respective midpoints
$K/2$ and $(K+e)/2$ would lie in the same interval $I$. Their
distance $e/2$ contradicts (6.8). This is a statement about any
two collisions on the whole curve, including four distinct
endpoints, not merely exclusion of collisions sharing a target.
It includes $\rho=0$.

An explicit arm choice uses only the known constants. For $\rho\ge1$
choose $a$; for $\rho<0$ choose $c$. For $0\le\rho<1$ choose $c$
exactly when

$$
0<K<2\quad\hbox{and}\quad
\frac13<\frac{K/2+2\rho/K}{e}<\frac12;                       \tag{6.9}
$$

otherwise choose $a$. Indeed an $a$ collision requires its midpoint
$K/2$ to be in $I$. If it is in $I$, a $c$ collision midpoint cannot
also be in $I$ by (6.8). Thus this rule is valid even when the
actual candidate subset is disconnected or omits the midpoint.
The proof concerns the containing legal interval, not convexity
of the candidate subset.

For chosen $a$, execute fifth $J$, read, then sixth $J$, read.
For chosen $c$, execute fifth $M$, read, then sixth $J$, read.
The chosen sixth response has a unique inverse on the whole known
class, giving the complete target. Existence of that inverse at an
actual reading comes from the actual candidate. No counterfactual
read is acquired. One may equivalently solve (6.7) for the unique
legal parameter and then interpolate the gain; arbitrary
deterministic inverse functions are permitted by Definition 1.1.

Finally suppose $\omega=0$ and $\kappa\ne0$. The identity
$d_6-b=H(6)(y+1)$ forces every candidate to have $H(6)=0$,
and then $\delta=b_0$. Thus $s=(j-b_0)/\kappa>0$ is common.
[II, Lemma 71.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
applies on exactly this same non-diagonal joint fifth fiber: at
fixed drift and sixth root, $H(7)$ is injective on complete targets.
The final $JJJ$ response is $b_0+sH(7)$, hence injective on the
entire class. All three $J$ atoms are immediately read at clocks
$5,6,7$. This is the zero-stratum argument already used in II,
Theorem 72.1; its hypothesis $\kappa\ne0$ has been retained.
No assertion about the $\omega=\kappa=0$ layer is required here. ∎

**推论 6.3（共同 b、d 承诺的整族及前一层消费者）。** Any known subset
$K\subseteq\mathcal C$ with either $\omega\ne0$ or
$\omega=0,\kappa\ne0$ has one at-most-eight-total-reading decoder,
without a cardinality bound. In particular it cannot have
$L_3(K,H_4(Y))$.

More generally, let $K$ be a known subset at the entire preceding
$H_3=(0,M,1,M,23/7,J,331/35)$. Suppose each reachable actual
fourth-$M$ response $Y$ has supplied known constants
$m_Y,j_Y,b_Y,d_Y$ placing its entire retained fiber in a class
(6.4) satisfying one of those two conditions. Then one policy
recovers all of $K$ within eight total readings.

Proof. Restriction of Theorem 6.2's single whole-class inverse recovers
the first known set. For the preceding history execute fourth $M$
and read $Y$. Apply the arm rule or zero-stratum $JJJ$ rule to that
whole retained set with its supplied constants. The fourth reading
is already acquired and is not repeated. The budgets are respectively
$5+2\le8$ or $5+3=8$ from $H_4$, and $4+1+3=8$ from $H_3$.
The constants are assumptions on each entire actual candidate fiber;
their existence or acquisition from unrestricted observations is
not a consequence of the policy. ∎

## 7. 数学来源、对应范围与未决边界

**约定 7.1（既有结果与新增的受约束纤维推导）。** The mathematical
dependencies and scopes are as follows.

| Source | Reused result and exact application |
| --- | --- |
| [II](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), Definitions 51.1, 56.1, 69.1–69.2; Theorem 70.1; Lemma 71.1; Theorem 72.1 | Complete targets, actual-fiber recursion and the $MMJM$ response chart; the curve and collision-midpoint mechanism is reused in Theorem 6.2. The new application strengthens common-$b,d_6$ matching to an injective arm on the whole known class, including disjoint pairs. Its zero layer is exactly the non-diagonal root-six application already in II. No duplicate general curve theorem is asserted. |
| [III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md), Theorem 4.1 and Proposition 7.1 | Its known-factor $g=(1+T^2)(a+bT)$ inverse and its fixed-word full-cubic collision retain their own scopes. Neither is an inverse for the arbitrary gains in (1.3) or an unrestricted adaptive lower bound. |
| [IV](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), Theorems 2.1, 3.1, 9.2–9.3 | The $JMMM$ and $MJMJ$ losing families have their own literal histories. Their complementary parents are distinct. The sixteen-slot local and 256-slot original-root systems impose simultaneous common-ancestor equations; neither has a feasibility verdict supplied here. |
| [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md), Definition 5.1; Theorems 5.2, 7.1; Definition 7.3 | The exact $JMMJ$ history, baseline-drift root-seven inverse, and terminal reconstruction are reused. Lemma 2.1 and Theorem 4.1 add exclusion of both arbitrary-drift sixth-gain strata on the actual fifth-$M$ child. Lemma 3.2 supplies the specific full rational sign certificate for the nonzero stratum. Theorem 5.1 removes the baseline-drift restriction from the small-child consumer while preserving its size hypothesis. |
| [VI](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md), Theorems 3.1–3.3, 5.1, 6.1–6.2 | Exactly three targets at the specified $MMJM$ parent already have the common-fifth bridge and an eight-reading policy, so a losing family there needs at least four targets. Its separate all-drift pair exclusion is for the literal $MJMMJ$ child, not (1.3). Neither theorem identifies these different histories. |
| [FIB Linear Gain-Ray Capacity and Hermite Readouts](FIB_LINEAR_GAIN_RAY_CAPACITY_AND_HERMITE_READOUTS.md), Theorems 3.3, 5.3, 7.1 and Section 8 | The fixed-acquisition gain-only threshold is $2d+3$; the countable-palette obstruction concerns fixed linear gain-ray outputs. At degree three this gives nine for that mechanism, not an unrestricted nonlinear complete-target lower bound. The gain-and-drift output and root-aware complete-target construction are separate tasks. |
| Yanjun Li, Kiryung Lee, Yoram Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1) | `literature-attested`: identification requires every compatible solution to belong to the specified transformation orbit, with a factor-orbit and conditional-fiber decomposition. Here trace one removes positive scaling only; drift remains a separate coordinate. No sample threshold or feedback acquisition result is imported. |
| Petra van den Bos, Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [Theorem 6.1 and Example 7](https://arxiv.org/html/1907.11034v2) | `literature-attested`: the whole-set adaptive distinguishing construction assumes a suspension automaton with mutually incompatible distinct states and injective splits. Example 7 shows failure of that equivalence when compatibility is allowed. These premises do not supply the policies here; their actual-fiber and whole-class hypotheses are proved or explicitly assumed above. |

The new constrained-history exclusions in Sections 2–4 and their
conditional consumers, and the whole-class application in Section 6,
are `repo-derived`. Interpolation, rank-one reconstruction, linear
trace coordinates, sign variation and Bernstein convex combinations
are established tools used inside these deductions. No external
priority or literature-completeness assertion is made.

**定义 7.2（保留的完整纤维与原根问题）。** The following questions remain
unresolved by these results. At the literal $JMMJ$ parent (1.3), can
an actual fifth-$M$ fiber with at least three fixed targets have
$L_2$, and can it be jointly realized with the losing child of the
other fifth arm to give $L_3$? Theorem 4.1 excludes a single
two-target $L_2$ set; it is not a decoder for every larger actual
fiber. On larger sets, different sixth actions may retain different
bad pairs, and those pairs need not have common endpoints.

At the separate $MMJM$ parent (6.1), the unrestricted question is
whether some entire $\mathcal F(H_4(Y))$ has $L_3$, or every such
fiber has a three-further-reading decoder. VI, Theorem 3.2 already
excludes every known set of at most three targets, so a losing family
must have at least four. Theorem 6.2 does not place an unrestricted
fiber in a common-$b,d_6$, common-$m,j$ class, and does not infer
those promises from an observed target. Arbitrary variable-response
fibers and the diagonal $\omega=\kappa=0$ extension of the stated
zero-stratum consumer remain outside its conclusion. Pairwise
separability does not extract a losing triple from a larger family.

The original full-domain alternative is still whether
$n_{\mathrm{det}}(3,0)\ge9$ or a lawful complete-target decoder with
at most eight total readings exists on all of $\mathcal W_3$.
Every initial action, actual history and early stop remains in that
question. The local size-bound policies and known-class promises
do not decide either original-root alternative. Neither a local
losing node nor a linear gain-readout obstruction supplies the
missing unrestricted original-root proof.

## 追加锚（本行以下为增补区）

## 8. 一个完整 H* 纤维的增益射线排除

**定义 8.1（固定历史及其完整插值坐标）。** Retain Definition 1.1
and fix the single literal history

$$
H_*=(0,J,24,M,48,M,312/5,J,48/5,M,-532/5),
\qquad \mathcal F_* =\mathcal F(H_*).                         \tag{8.1}
$$

Its cumulative matrices at original clocks zero through five are
exactly the six matrices in (1.5). No initial-root or drift condition
is imposed on $\mathcal F_*$. For any legal source put

$$
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad
u=\operatorname{tr}(JP)=b+c>0,\qquad
v=\operatorname{tr}(LP)=1+b>1.                               \tag{8.2}
$$

For a source and a real drift $d$, define $G_{P,d}$ by interpolation
at the four original clocks $0,1,2,3$, with values

$$
(q_0,q_1,q_2,q_3)
=\left(-d,\frac{24-d}{u},\frac{48-d}{v},
                    \frac{312/5-d}{u+v}\right).
\tag{8.3}
$$

Explicitly, $G_{P,d}(T)=\sum_{i=0}^3q_i\ell_i(T)$, where

$$
\begin{aligned}
\ell_0&=-(T-1)(T-2)(T-3)/6,&
\ell_1&=T(T-2)(T-3)/2,\\
\ell_2&=-T(T-1)(T-3)/2,&
\ell_3&=T(T-1)(T-2)/6.
\end{aligned}                                                \tag{8.4}
$$

This is the unique gain of degree at most three giving the first four
readings with this source and drift. It cannot be identically zero:
otherwise those readings would all equal $d$. In particular these
coordinates retain every lower degree, sign and sampled-root case.
Write $G_i=G_{P,d}(i)$. The useful evaluations are

$$
\begin{pmatrix}G_4\\G_5\\G_6\end{pmatrix}
=\begin{pmatrix}-1&4&-6&4\\-4&15&-20&10\\-10&36&-45&20\end{pmatrix}
 \begin{pmatrix}q_0\\q_1\\q_2\\q_3\end{pmatrix}.              \tag{8.5}
$$

Define the following response functions of the same fixed world:

$$
\begin{aligned}
\mathcal Y(P,d)&=d+G_4(1+a+u),\\
\mathcal Z(P,d)&=d+G_5(u+2v-a),\\
S_J(P,d)&=d+G_6(2+2a+2u-v),\\
S_M(P,d)&=d+G_6(1+2u+2v).
\end{aligned}                                                \tag{8.6}
$$

The first two are the fourth-$J$ and fifth-$M$ readings. The last two
are alternative sixth readings, since
$JQ=\left(\begin{smallmatrix}3&2\\1&1\end{smallmatrix}\right)$ and
$MQ=\left(\begin{smallmatrix}3&2\\4&3\end{smallmatrix}\right)$.
All their trace factors are positive for a legal source. Thus
$\mathcal F_*$ is exactly the set of triples
$(P,G_{P,d},d)$ with a legal source and
$\mathcal Y=48/5,\mathcal Z=-532/5$. No equation at four or five is
omitted by the interpolation. Defining both sixth response functions
does not acquire both readings.

**定理 8.2（完整 H* 纤维中每条增益射线至多一个目标）。** If
$W_1,W_2\in\mathcal F_*$ and their nonzero gains are proportional over
$\mathbb R$, then $W_1=W_2$. There is no restriction on their drifts.

Proof. Let $d_i$ be the drift of $W_i$. Write $g_i=c_i h$, with
$c_i\ne0$, $h\ne0$, $\deg h\le3$, and $R_i=c_iP_i$. Let

$$
(y_0,\ldots,y_5)=(0,24,48,312/5,48/5,-532/5).
\tag{8.7}
$$

These six readings are distinct. A sampled zero $h(k)=0$ forces
$d_1=d_2=y_k$. If the drifts agree, there is at most one such sampled
zero. At the other at least five clocks, the common readings give
$\operatorname{tr}(A_k(R_1-R_2))=0$. Every five of the matrices in
(1.5) span $\operatorname{Mat}_2(\mathbb R)$, as established in
Lemma 2.1. Nondegeneracy of the trace pairing gives $R_1=R_2$.
Their traces are $c_1,c_2$, so trace normalization then gives
$c_1=c_2$, $P_1=P_2$, and the same entire gain and drift. This also
handles all sampled-zero cases.

Suppose instead $d_1\ne d_2$. All six $h(k)$ are now nonzero. Set

$$
S=\frac{R_1-R_2}{d_1-d_2},\qquad V=R_1-d_1S.
\tag{8.8}
$$

The common readings imply

$$
\operatorname{tr}(A_kS)=-\frac1{h(k)},\qquad
\operatorname{tr}(A_kV)=\frac{y_k}{h(k)}.                    \tag{8.9}
$$

These are auxiliary real matrices, with no asserted source legality.
Rescale the representation $c_i h$ so that $h(1)=1$. The identity
$A_3=J+L$ applied to both matrices gives

$$
\frac1{h(3)}=1+\frac1{h(2)},\qquad
\frac{312/5}{h(3)}=24+\frac{48}{h(2)}.
\tag{8.10}
$$

Solving yields $h(2)=-3/8$ and $h(3)=-3/5$. Cubic interpolation,
including lower degrees, now gives

$$
B:=h(4)=\frac{77}{20}-h(0),\qquad
h(5)=\frac{33}{2}-4h(0)=4B+\frac{11}{10}.                    \tag{8.11}
$$

Both quantities are nonzero. Applying $Q=I+2J+2L-C$ to $V$ gives

$$
\frac{-532/5}{4B+11/10}=-208-\frac{48/5}{B}.
\tag{8.12}
$$

Clearing these already nonzero denominators requires
$5200B^2+1005B+66=0$. The exact everywhere-positive certificate is

$$
20800(5200B^2+1005B+66)
=(10400B+1005)^2+362775>0.                                  \tag{8.13}
$$

This contradiction excludes unequal drifts. No sign of $c_i$, rank
condition on an auxiliary matrix, or nonzero-gain-sample promise was
used to infer existence of a physical world. ∎

**推论 8.3（互异祖先读数下的负判别式延伸）。** Consider
$H_{JM}(Y,z)$ with $D_0=0,\lambda=1$. Suppose its six readings
$0,24,48,312/5,Y,z$ are pairwise distinct and

$$
\left(\frac{1144}{5}+4Y+z\right)^2
       -4\cdot832\cdot\frac{11Y}{10}<0.                     \tag{8.14}
$$

Then proportional gains again force identical complete targets on
that entire fiber.

Proof. Distinct readings give exactly the same sampled-zero and
equal-drift argument. In the unequal-drift case, (8.10)–(8.11)
are unchanged. The final identity for $V$ is
$z/(4B+11/10)=-208-Y/B$, requiring

$$
832B^2+\left(\frac{1144}{5}+4Y+z\right)B+\frac{11Y}{10}=0.
\tag{8.15}
$$

Its leading coefficient is positive and its discriminant is negative,
so it has no real solution. At $(Y,z)=(48/5,-532/5)$ the discriminant
is $-232176/25$, and (8.15) is a positive scalar multiple of the
quadratic in (8.13). Nonnegative discriminant is not asserted to
give actual collisions. Neither result supplies the unknown gain
ray from the readings, or excludes collisions of nonproportional
gains. ∎

## 9. 完整交叉切片及其远端代数目标

**定理 9.1（包括闭源极限的精确 u=1 切片）。** Let $\theta$ be
the unique root in $[0,1]$ of

$$
C_*(b)=45b^3+141b^2+2464b-56.
\tag{9.1}
$$

It satisfies

$$
\frac{22697}{10^6}<\theta<\frac{22698}{10^6}.                 \tag{9.2}
$$

The entire set $\mathcal F_*\cap\{\operatorname{tr}(JP)=1\}$
consists of exactly the following two complete targets:

$$
\begin{aligned}
W_0&=(P_0,g_0,0),&
P_0&=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},&
g_0(T)&=\frac4{25}T(T^2-53T+202),\\
W_\theta&=(P_\theta,g_\theta,d_\theta),&
P_\theta&=\begin{pmatrix}1-\theta&\theta\\1-\theta&\theta\end{pmatrix},&
d_\theta&=\frac{48}{5}
 \frac{10\theta^3-3\theta^2-89\theta+44}
      {3\theta^3-\theta^2-20\theta+8}.
\end{aligned}                                                \tag{9.3}
$$

Here $g_\theta$ is specified completely by its four values

$$
\left(-d_\theta,\ 24-d_\theta,
 \frac{48-d_\theta}{1+\theta},
 \frac{312/5-d_\theta}{2+\theta}\right)
\quad\text{at }0,1,2,3,                                    \tag{9.4}
$$

using (8.4). The same two targets exhaust the solutions if source
positivity is relaxed to entrywise nonnegativity while retaining
trace one, determinant zero, $u=1$, and all six ancestor equations.
Thus there is no compatible source-boundary limit on this slice.

Proof. In (8.2), $u=1$ gives $c=1-b$. The determinant equation is

$$
a(1-a)=b(1-b),\qquad (a-b)(1-a-b)=0.
\tag{9.5}
$$

Consequently both and all source branches are $a=b$ and $a=1-b$,
with $0<b<1$. For the nonnegative version use $0\le b\le1$;
(9.5) still exhausts the sources. The six trace factors are
$1,1,1+b,2+b,2+a,3+2b-a$, all strictly positive even at those
closed-interval endpoints.

Put

$$
\begin{aligned}
D&=(b+1)(b+2),\\
A_4&=\frac{96}{5}(5b^2+13b-7),&B_4&=2-7b-3b^2,\\
A_5&=24(15b^2+31b-24),&B_5&=8-23b-11b^2,\\
t_4&=2+a,&t_5&=3+2b-a,\\
Q_i&=D+t_iB_i,&N_i&=y_iD-t_iA_i\quad(i=4,5),
\end{aligned}
\qquad y_4=48/5,\quad y_5=-532/5.                            \tag{9.6}
$$

The first four readings force precisely the interpolant (9.4) with
$b,d$ in place of $\theta,d_\theta$. By (8.5),
$DG_i=A_i+dB_i$ for $i=4,5$. Hence the two remaining actual
ancestor equations are exactly

$$
dQ_4=N_4,\qquad dQ_5=N_5.                                   \tag{9.7}
$$

Multiplication of the displayed polynomials gives the identities

$$
N_4Q_5-N_5Q_4=
\begin{cases}
\dfrac{12}{5}(2b-1)D(334+157b-4b^2-5b^3),&a=b,\\[2mm]
\dfrac45(2b-1)D C_*(b),&a=1-b.
\end{cases}                                                 \tag{9.8}
$$

On $[0,1]$, $D>0$ and the first residual cubic is at least $325$.
The second has derivative $135b^2+282b+2464>0$, with endpoint values
$-56,2594$. Moreover its values at the left and right endpoints
of (9.2) are respectively

$$
-\frac{285830572174143}{200000000000000000},\qquad
 \frac{26032934573941}{25000000000000000}.                    \tag{9.9}
$$

Thus the only possible parameters are $b=1/2$ on either branch,
and $b=\theta$ on the branch $a=1-b$. This conclusion includes
the closed endpoints and precedes any division by $Q_i$.

At $b=a=1/2$, $Q_4=-15/8$ and $N_4=0$, so $d=0$ and interpolation
gives $g_0$. On the second branch,

$$
Q_4=3b^3-b^2-20b+8,\qquad
N_4=\frac{48}{5}(10b^3-3b^2-89b+44).
\tag{9.10}
$$

For $b$ in (9.2), $Q_4>7$. Therefore $d=N_4/Q_4$ is lawful and
gives exactly $d_\theta$. Conversely, at either candidate, (9.8)
vanishes and $Q_4\ne0$. Substituting $d=N_4/Q_4$ into (9.8)
gives $dQ_5=N_5$, without division by $Q_5$. Both remaining
ancestors are satisfied. The four earlier ones hold by the single
fixed interpolant, not by changing the world at a later clock.

Both displayed matrices are strictly positive, trace one and rank
one. The interpolants are nonzero, as already noted after (8.4).
This proves existence and exhaustion, including every potential
zero divisor, sampled root and degree drop, and proves the
closed-source assertion. ∎

**推论 9.2（远端符号界及实际第六读逆）。** The algebraic target has

$$
53<d_\theta<54,\qquad -199<g_\theta(6)<-197,
\tag{9.11}
$$

and its actual sixth responses satisfy

$$
-922<S_J(W_\theta)<-921,\qquad
-945<S_M(W_\theta)<-944.                                    \tag{9.12}
$$

Either sixth atom recovers the entire known slice of Theorem 9.1
with seven total readings. Execute either chosen sixth atom and
return $W_\theta$ when its reading is below $-800$, and $W_0$
otherwise.

Proof. On the remote branch, the sixth trace factors in (8.6) are
$5-3\theta$ and $5+2\theta$. The gain formula is

$$
g_\theta(6)=864-26d_\theta
 +\frac{45(d_\theta-48)}{1+\theta}
 +\frac{20(312/5-d_\theta)}{2+\theta}.                        \tag{9.13}
$$

For explicit rational interval bounds, partition the interval in
(9.2) into

$$
I_k=\left[\frac{64\cdot22697+k}{64000000},
           \frac{64\cdot22697+k+1}{64000000}\right],
\qquad 0\le k<64.                                          \tag{9.14}
$$

Evaluate (9.10), $d=N_4/Q_4$, (9.13), and then
$d+g(6)(5-3b),d+g(6)(5+2b)$ on each $I_k$. Horner evaluation
and rational interval addition, multiplication, and reciprocal give
the following containing intervals, uniformly for every $k$:

$$
\begin{array}{c|c}
\text{expression}&\text{containing open interval}\\ \hline
Q_4&(7,9)\\
d&(53,54)\\
g(6)&(-199,-197)\\
d+g(6)(5-3b)&(-922,-921)\\
d+g(6)(5+2b)&(-945,-944).
\end{array}                                                 \tag{9.15}
$$

All input endpoints and all coefficients in this finite interval
certificate are given in (9.10), (9.13)–(9.14). For multiplication
take the least and greatest of the four endpoint products; for a
nonzero interval $[r,s]$ use reciprocal $[1/s,1/r]$. Every reciprocal
here has positive denominator, including $Q_4>7$, $1+b>1$ and
$2+b>2$. These rules establish (9.11)–(9.12) on their union.

In particular $g_\theta(0),g_\theta(1),g_\theta(2)<0$ and
$g_\theta(3)>0$, by (9.4) and $53<d_\theta<54<312/5$.
The positive fourth and fifth trace factors and their ancestor
equations give $g_\theta(4),g_\theta(5)<0$; (9.11) gives the
same strict sign at six. Thus the remote target has a nonzero
initial sample and a different ancestor sign pattern from $W_0$.

For the base world, (8.5)–(8.6) give

$$
S_J(W_0)=-1344/5,\qquad S_M(W_0)=-2304/5.                   \tag{9.16}
$$

Both exceed $-800$, whereas both remote responses are below it.
Theorem 9.1 exhausts the slice, so the stated inverse returns the
complete actual target. Execute only the selected sixth atom and
immediately read it at original clock six. The already acquired
six readings plus this one give seven. The two distinct targets
share $H_*$, so no answer before this added reading can recover
the whole slice. The source-slice label is a supplied class
restriction, not an observation inferred from $H_*$. ∎

## 10. 两个局部逆与整个源带的无逃逸桥梁

**引理 10.1（两个实际世界的响应雅可比证书）。** Use the bijective
positive-source chart

$$
P(\alpha,\beta)=\frac1{1+\alpha\beta}
 \begin{pmatrix}1&\beta\\\alpha&\alpha\beta\end{pmatrix},
\qquad \alpha,\beta>0.                                    \tag{10.1}
$$

Its inverse is $\alpha=P_{21}/P_{11}$,
$\beta=P_{12}/P_{11}$; the rank-one equation determines the fourth
entry and trace one determines the denominator. Let
$\mathcal T_J=(\mathcal Y,\mathcal Z,S_J)$ and
$\mathcal T_M=(\mathcal Y,\mathcal Z,S_M)$, using the interpolant
and response functions of Definition 8.1. Their coordinate domain is
$\{\alpha,\beta>0,d\in\mathbb R\}$. Both are smooth there.
At $x_0=(1,1,0)$ their four response gradients, with columns
$\alpha,\beta,d$, are

$$
\begin{array}{c|rrr}
&\partial_\alpha&\partial_\beta&\partial_d\\ \hline
\mathcal Y&-56&1352/25&-1/2\\
\mathcal Z&-20878/75&19738/75&-29/6\\
S_J&-16152/25&18072/25&-13\\
S_M&-27552/25&27552/25&-23.
\end{array}                                                 \tag{10.2}
$$

In particular,

$$
\det\frac{\partial(\mathcal Y,\mathcal Z)}{\partial(\alpha,\beta)}
=\frac{197952}{625},\quad
\det D\mathcal T_J(x_0)=-\frac{382512}{25},\quad
\det D\mathcal T_M(x_0)=-\frac{1142016}{125}.                 \tag{10.3}
$$

At $x_\theta=(1,\theta/(1-\theta),d_\theta)$,
$D\mathcal T_J$ has its nine entries in the respective open
intervals below; every endpoint in the table is divided by $100$:

$$
\begin{pmatrix}
(29567,29569)&(-9918,-9916)&(364,365)\\
(75219,75223)&(-46913,-46906)&(847,849)\\
(440914,440931)&(-73660,-73642)&(4101,4102)
\end{pmatrix}.                                             \tag{10.4}
$$

Consequently

$$
\frac{502852949701}{500000}
\le\det D\mathcal T_J(x_\theta)
\le\frac{1052660174081}{1000000},                            \tag{10.5}
$$

so this determinant too is nonzero.

Proof. Write $h=1+\alpha\beta$. The source coordinates and their
partial derivatives are

$$
\begin{gathered}
a=h^{-1},\qquad u=(\alpha+\beta)/h,\qquad v=1+\beta/h,\\
(a_\alpha,a_\beta)=(-\beta,-\alpha)/h^2,\\
(u_\alpha,u_\beta)=(1-\beta^2,1-\alpha^2)/h^2,\qquad
(v_\alpha,v_\beta)=(-\beta^2,1)/h^2.
\end{gathered}                                              \tag{10.6}
$$

For $\tau=(1,u,v,u+v)$ and $y=(0,24,48,312/5)$, the interpolation
samples satisfy, for $r=\alpha,\beta$,

$$
(q_i)_r=-\frac{(y_i-d)(\tau_i)_r}{\tau_i^2},\qquad
(q_i)_d=-\frac1{\tau_i}.                                   \tag{10.7}
$$

This also gives $(q_0)_r=0,(q_0)_d=-1$. Apply (8.5) to these
derivatives. If a response is $d+G_it$, its $r$ derivative is
$t(G_i)_r+G_it_r$ for $r=\alpha,\beta$, and its $d$ derivative
is $1+t(G_i)_d$. Substituting $x_0$ gives (10.2), and determinant
expansion gives (10.3).

For (10.4), differentiate with $\alpha,\beta,d$ independent first.
Then in (10.6)–(10.7), (8.5)–(8.6) substitute
$\alpha=1$, $\beta=b/(1-b)$ and the rational function
$d=N_4(b)/Q_4(b)$ from (9.10). On each rational interval $I_k$ of
(9.14), the interval rules in Corollary 9.2 put the nine resulting
entries strictly between the endpoints in (10.4). The denominators
$1-b,h,u,v,u+v,Q_4$ are positive on these intervals. The derivative
with respect to $d$ is a partial derivative, not a derivative along
the substituted curve $d=N_4(b)/Q_4(b)$.

Finally let $E_{ij}$ denote the closed interval obtained by dividing
the corresponding endpoints of (10.4) by $100$. Applying the same
interval rules to the six signed products

$$
E_{11}E_{22}E_{33}+E_{12}E_{23}E_{31}+E_{13}E_{21}E_{32}
-E_{13}E_{22}E_{31}-E_{12}E_{21}E_{33}-E_{11}E_{23}E_{32}
\tag{10.8}
$$

gives exactly the endpoint interval in (10.5). Its lower endpoint
is positive. This is a finite rational certificate for the remote
Jacobian, without a generic-rank assumption. ∎

**定理 10.2（整个充分小源带上的实际单读恢复）。** There exists
$\varepsilon>0$ such that the sixth-$J$ response is injective on
the entire set

$$
K_\varepsilon=
\{W\in\mathcal F_*:|\operatorname{tr}(JP)-1|<\varepsilon\}.
\tag{10.9}
$$

One fixed sixth $J$ and its immediate reading recover the complete
target for every member of this known set, with seven total
readings. No additional restriction on drift, gain signs, roots,
degrees or cardinality is imposed inside the band.

Proof. By Lemma 10.1 and the inverse function theorem, there are open
coordinate neighborhoods $V_0,V_\theta$ of $x_0,x_\theta$ on each
of which $\mathcal T_J$ is injective and has a smooth inverse onto
its image. The distinct base responses (9.12), (9.16) allow these
neighborhoods to be shrunk so that

$$
S_J(V_0)\subset(-400,-200),\qquad
S_J(V_\theta)\subset(-1000,-900).                            \tag{10.10}
$$

On the compatible part of either neighborhood, $\mathcal Y,\mathcal Z$
are fixed. Thus $S_J$ alone is injective on each such entire part,
and the two response ranges are disjoint. It remains to prove that
some whole band (10.9) is contained in their union.

Suppose no such band is contained there. Choose compatible worlds
$W_n=(P_n,g_n,d_n)$ outside both neighborhoods with $u_n\to1$.
Write $P_n$ as in (8.2). Since $0<a_n<1$ and
$0<b_n,c_n<u_n$, a subsequence of their source entries converges
to a nonnegative matrix

$$
P_\infty=\begin{pmatrix}a&b\\1-b&1-a\end{pmatrix},\qquad
0\le a,b\le1,\qquad a(1-a)=b(1-b).                         \tag{10.11}
$$

Here trace and determinant pass to the limit. In particular
$v_n=1+b_n\to1+b\ge1$, and $u_n,v_n,u_n+v_n$ stay bounded away
from zero. This compactness does not assume the source-chart
parameters stay bounded.

We first exclude unbounded drift. From (8.3)–(8.5) write
$G_i=\gamma_i+d\kappa_i$ for $i=4,5$, where

$$
\begin{aligned}
\gamma_4&=96/u-288/v+(1248/5)/(u+v),&
\kappa_4&=1-4/u+6/v-4/(u+v),\\
\gamma_5&=360/u-960/v+624/(u+v),&
\kappa_5&=4-15/u+20/v-10/(u+v).
\end{aligned}                                              \tag{10.12}
$$

For $t_4=1+a+u,t_5=u+2v-a$, the last two ancestor equations are

$$
d(1+t_i\kappa_i)=y_i-t_i\gamma_i,\qquad i=4,5.
\tag{10.13}
$$

Their right sides remain bounded along the convergent sources.
If a further subsequence had $|d_n|\to\infty$, dividing (10.13)
by $d_n$ and passing to the limit would give
$1+t_4\kappa_4=1+t_5\kappa_5=0$ at (10.11). At $u=1$ these
two expressions are precisely $Q_4/D,Q_5/D$ in (9.6). Thus
$Q_4=Q_5=0$, so the residual (9.8) vanishes. Its closed-interval
factorization forces $b=1/2$ or $b=\theta$, with the branch
conditions of Theorem 9.1. At these candidates $Q_4=-15/8$ or
$Q_4>7$, respectively, a contradiction. Therefore the drift
sequence is bounded even along subsequences whose sources approach
the boundary.

Take a further subsequence with $d_n\to d$. The first four
interpolation samples then converge, because their trace denominators
stay positive. The gain coefficients converge by (8.4). The limiting
gain is nonzero: if it were zero, the limiting initial and first
readings would give both $d=0$ and $d=24$. All six ancestor
equations pass to the limit. The closed-source part of Theorem 9.1
now forces this limit to be $W_0$ or $W_\theta$. Both have strictly
positive sources. The inverse chart in Lemma 10.1 is continuous
there, so the coordinate sequence eventually belongs to $V_0$ or
$V_\theta$. This contradicts its choice outside both. Hence a
positive band radius with the required containment exists.

For this radius, $S_J$ is injective on each of the two retained
parts and their ranges are disjoint by (10.10), proving injectivity
on all of $K_\varepsilon$. An actual read $s$ selects $V_\theta$
when $s<-800$ and $V_0$ otherwise. Apply that neighborhood's inverse
of $\mathcal T_J$ to $(48/5,-532/5,s)$, then (10.1) and (8.4),
to return the complete $(P,g,d)$. Actual membership supplies existence
of this inverse value; uniqueness is on the whole promised band.
Only sixth $J$ is executed and read, so the budget is $6+1=7$.

The band contains actual nonzero-drift continua, not just the two
slice points. Indeed the first minor in (10.3) gives, by the
implicit function theorem, the entire local compatible fiber at
$W_0$ as a graph $(\alpha(d),\beta(d),d)$ for $d$ in an interval
about zero. Differentiating its fixed $\mathcal Y,\mathcal Z$
equations gives

$$
\alpha'(0)=-\frac{81125}{197952},\qquad
\beta'(0)=-\frac{82175}{197952},\qquad
\frac{dS_J}{dd}(0)=-\frac{199225}{4124},\qquad
\frac{dS_M}{dd}(0)=-\frac{29740}{1031}.                       \tag{10.14}
$$

Thus both sixth responses are locally strictly decreasing after
shrinking the interval. This is the usual implicit-function method
around the base world, now with its actual response transversality;
its existence alone is not a global inverse. The identity

$$
u-1=-\frac{(\alpha-1)(\beta-1)}{1+\alpha\beta}               \tag{10.15}
$$

and the two nonzero source velocities show $u<1$ for sufficiently
small nonzero $d$. These worlds have $g(0)=-d\ne0$ and lie in
$K_\varepsilon$ by continuity. Thus neither the initial-root
condition nor the exact slice label is determined by $H_*$. The
whole-band conclusion instead uses the closed-slice classification,
both local inverses, disjoint response ranges, and the no-escape
argument above. ∎

## 11. 仿射运输、数学接口与完整问题的边界

**推论 11.1（任意基线及两种非零尺度符号）。** Fix
$D_0\in\mathbb R$, $\lambda\in\mathbb R\setminus\{0\}$ and set

$$
H_*^{D_0,\lambda}=
(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5,
 J,D_0+48\lambda/5,M,D_0-532\lambda/5).                      \tag{11.1}
$$

Theorems 8.2, 9.1 and 10.2 transport to this entire literal history
under

$$
(P,g,d)\longmapsto(P,\lambda g,D_0+\lambda d).
\tag{11.2}
$$

In particular the same source radius $\varepsilon$ gives a
seven-total-reading decoder on the entire corresponding known band.

Proof. This is the bijective normalization (1.4). For every original
clock and every action word, its readings satisfy
$z_i^{\rm aff}=D_0+\lambda z_i$. Sources, strict positivity, rank,
degrees, roots, target distinction and source-band membership are
preserved. For either sign of $\lambda$, normalize the actual sixth
read as $s=(z_6^{\rm aff}-D_0)/\lambda$, apply the inverse above,
and return (11.2). In particular its branch test is $s<-800$;
using the unnormalized inequality without reversing it when
$\lambda<0$ would not be this policy. The normalization is algebra
on acquired readings, not another sensor or acquisition. The history
already contains six immediate readings and only one $J$ and read
are added at clock six. The extension (8.14) likewise transports
with $Y,z$ interpreted as normalized readings. ∎

**约定 11.2（所用数学结果的精确对应）。** The interpolation and
trace-coordinate methods above use the following interfaces with
their stated scopes.

| Mathematical source | Correspondence and restriction |
| --- | --- |
| Definitions 1.1–1.3 and Lemma 2.1 of this volume | Complete targets, original-clock acquisition, the six actual matrices and their every-five spanning property; only this algebraic spanning fact is used in the proportional-gain proof. Theorem 4.1 already excludes two-target $L_2$ on every specified fifth-$M$ fiber, without a gain-ray promise; it is not reproved as a larger-family theorem. |
| [VI, Theorem 3.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md) | Recovery of every known set of at most three targets at its distinct $MMJM$ parent. Its size hypothesis and literal history are retained; it imposes no bound on the cardinality of $\mathcal F_*$. |
| [FIB Moving-Trace Recovery and Sharp Calibrated Continuations, Lemmas 3.1–3.2 and Theorems 5.1–5.2](FIB_MOVING_TRACE_RECOVERY_AND_SHARP_CALIBRATED_CONTINUATIONS.md) | Trace bases and the two-branch spectral crossing are existing structures. Here (9.5) evaluates the $J$ crossing against every $H_*$ ancestor. The moving-trace pure-$M$ calibration and its prescribed-prefix sharpness are not hypotheses for an unrestricted eight-reading bound. |
| Li–Lee–Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1) | Identification requires every compatible solution to belong to the specified transformation orbit, with factor-orbit and conditional-fiber conditions. Here trace one removes positive source/gain scaling and leaves drift as a separate coordinate. The proportional-gain exclusion does not acquire the gain orbit. No bilinear sampling threshold is applied. |
| Breiding–Gesmundo–Michałek–Vannieuwenhoven, *Algebraic compressed sensing*, [Answers 7–9](https://arxiv.org/html/2108.13208v2) | The generic-map and generic-point identification statements have different quantifiers from everywhere identification for prescribed atoms. No dimension threshold from those results is used here; the passage from local inverses to the entire band is the explicit compactness argument of Theorem 10.2. |

The base world and the implicit-function construction are supporting
examples and standard methods. The substantive compatibility
calculations are the full-fiber positive quadratic certificate, the
exhaustive two-branch ancestor calculation with its remote target,
and the closed-source and unbounded-drift exclusion that joins both
local inverses on the whole band. Polynomial interpolation, the
implicit and inverse function theorems, elementary trace linear
algebra, rational interval bounds and finite-dimensional compactness
are established mathematical tools. These applications carry no
external-priority assertion.

**开放问题 11.3（带外纤维与不受限原根目标）。** The radius in
Theorem 10.2 is existential; no numerical radius, stability modulus
or computational cost bound is specified. Band membership is a known
input restriction. The history does not thereby certify that its
actual world lies in that band, and no collision between a band
world and a world outside it has been excluded. At $H_*$, every
$L_2$ family must contain a world outside this band, but such a
necessary condition neither realizes a losing family nor supplies
an inverse on all of $\mathcal F_*$. The full-fiber gain-ray theorem
still permits families of different gain rays.

For a complete two-further-reading inverse on $\mathcal F_*$ one
must select a single sixth atom and, for every actual response, stop
on a singleton or select one seventh atom injective on that entire
retained fiber. Alternatively an $L_2$ witness must use fixed legal
worlds realizing every ancestor simultaneously, with losing actual
children for both sixth atoms. Different children and terminal
actions can use different collision pairs, including disjoint pairs;
constant-response arms also remain in scope. Neither alternative
is supplied by the slice or band inverse.

The exact-slice and band results concern (8.1) and its affine copies
(11.1), not arbitrary $Y,z$ in (1.3). Corollary 8.3 provides only
its explicit distinct-reading, negative-discriminant exclusion on
some further histories. The complementary parent arms, other
original histories and early stops retain their own obligations.
At the distinct $MMJM$ parent, the unrestricted four-target and
larger $L_3$ question and the whole-fiber three-read inverse remain
the questions of Section 7. The $H_*$ restrictions do not impose a
common gain, drift or source stratum on that distinct parent.

The full original-clock alternative remains
$n_{\mathrm{det}}(3,0)\ge9$ versus a lawful decoder for every
$(P,g,\delta)\in\mathcal W_3$ in at most eight total readings.
It quantifies over all initial actions and actual branches, all
constant drifts, every nonzero cubic-or-lower gain with all signs
and sampled or repeated roots, and arbitrary deterministic policies
without regularity assumptions. The three conclusions above give
neither an original-root lower-bound tree nor an unrestricted
eight-reading decoder.

## 追加锚（本行以下为增补区）

## 12. JMMJ 整个根六父类的实际有限子纤维

**定义 12.1（根六承诺与逐时钟的 J 延续）。** Retain the complete
worlds, original clocks and deterministic policies of Definition 1.1.
For arbitrary $D_0,Y\in\mathbb R$ and $\lambda\ne0$, write the
literal parent of Definition 1.2 as

$$
H_p=H_J(Y)
=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5,J,Y).
\tag{12.1}
$$

Put $f=g/\lambda$, $d=(\delta-D_0)/\lambda$ and
$y=(Y-D_0)/\lambda$, as in (1.4). The entire promised class is

$$
\mathcal C_6(H_p)=\{(P,g,\delta)\in\mathcal F(H_p):f(6)=0\}.
\tag{12.2}
$$

A known subset $K\subseteq\mathcal C_6(H_p)$ may have any
cardinality and may contain different drifts. Membership in (12.2)
is an input premise; it is not an observation obtained from $H_p$.
In particular neither $d=0$ nor $f(7)\ne0$ is imposed.

Use the source coordinates

$$
\begin{gathered}
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
\ell=1+u>1,\qquad k=\frac{u+v}{\ell}>0,\\
u=\ell-1,\qquad v=(k-1)\ell+1>0,\qquad
0<r<1,\qquad uv=r(1-r).
\end{gathered}
\tag{12.3}
$$

These conditions are equivalent to strict entrywise positivity,
rank one and trace one; no equality between $u$ and $v$ is required.
The matrices $L,C,Q$ are those of (1.5). After the actual fifth $J$
and sixth $J$, the cumulative matrices and their trace factors are

$$
\begin{array}{c|c|c}
\text{clock}&A_i&\operatorname{tr}(A_iP)\\ \hline
0&I&1\\
1&J&k\ell\\
2&L&\ell\\
3&J+L&(k+1)\ell\\
4&C&1+r+k\ell\\
5&J+L&(k+1)\ell\\
6&C&1+r+k\ell\\
7\text{ after }J&J+L&(k+1)\ell\\
7\text{ after }M&Q&(k+2)\ell-r.
\end{array}
\tag{12.4}
$$

Indeed $JC=J+L$ and $J(J+L)=C$. In particular $Q$ here is the
seventh-$M$ state of the word $JMMJJJM$; no fifth-$M$ response is
part of this continuation. Every displayed trace is positive.
Write $x=(z_5-D_0)/\lambda$ and $w=(z_6-D_0)/\lambda$ for the
normalized readings actually acquired at clocks five and six.
For arbitrary worlds on this history,

$$
x=d+f(5)(k+1)\ell,\qquad
w=d+f(6)(1+r+k\ell).
\tag{12.5}
$$

On (12.2) the actual sixth reading is therefore $z_6=\delta$ and
$w=d$. For each $x,d\in\mathbb R$, let

$$
\mathcal C_{x,d}
=\mathcal C_6(H_p)\cap
\mathcal F(H_p,J,D_0+\lambda x,J,D_0+\lambda d).
\tag{12.6}
$$

This definition retains all five parent readings and both subsequent
actual readings on the same worlds. Its second subscript is both an
acquired normalized response and, within this promised class, the
normalized target drift.

**定义 12.2（完整插值与根六系数）。** For the coordinates (12.3), the
first four normalized readings give the gain samples

$$
(\alpha_0,\alpha_1,\alpha_2,\alpha_3)
=\left(-d,\frac{24-d}{k\ell},\frac{48-d}{\ell},
                      \frac{312/5-d}{(k+1)\ell}\right).
\tag{12.7}
$$

The gain is the unique polynomial of degree at most three with these
values at $0,1,2,3$: $f(T)=\sum_{i=0}^3\alpha_i\ell_i(T)$, with
the basis (8.4). This is standard Lagrange interpolation, as in
[NIST DLMF, §3.3(i), equation (3.3.1)](https://dlmf.nist.gov/3.3.E1),
with $n=3$, nodes $z_i=i$ and sample values $\alpha_i$. It is used
inside the following deductions, not asserted as a new result.
All denominators in (12.7) are positive. The interpolant cannot be
zero, since the normalized readings at zero and one are different.

Set $D=\ell k(k+1)>0$, and define

$$
\begin{aligned}
N&=(2160-45d)k^2+(48+11d)k+36d-864,\\
p_4&=\frac32(d-48)k^2+\frac{624-9d}{10}k+\frac{48-2d}{5},\\
p_5&=2(d-48)k^2+\frac{216-3d}{5}k+\frac{72-3d}{5},\\
p_7&=6(48-d)k^2+(d-72)k+2d-48.
\end{aligned}
\tag{12.8}
$$

**引理 12.3（每个实际第五 J、第六 J 子纤维至多两个完整世界）。**
For every $x,d\in\mathbb R$,

$$
|\mathcal C_{x,d}|\le2.
\tag{12.9}
$$

This counts complete triples $(P,g,\delta)$, including every source
asymmetry, gain sign, sampled or multiple root and degree drop.

Proof. Evaluation of the interpolant (12.7) gives

$$
\begin{pmatrix}f(4)\\f(5)\\f(6)\\f(7)\end{pmatrix}
=\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}\alpha_0\\\alpha_1\\\alpha_2\\\alpha_3\end{pmatrix}.
\tag{12.10}
$$

Multiplying by $D$ and subtracting $1/10,2/5,2$ times the sixth
row from the fourth, fifth and seventh rows respectively gives the
identities

$$
Df(6)=10dD-N,\qquad
D\bigl(f(i)-a_i f(6)\bigr)=p_i,
\quad (i,a_i)=(4,1/10),(5,2/5),(7,2).
\tag{12.11}
$$

Consequently every promised world satisfies

$$
10d\ell k(k+1)=N,\qquad
f(i)=\frac{p_i}{\ell k(k+1)}\ (i=4,5,7),\qquad
x=d+\frac{p_5}{k}.
\tag{12.12}
$$

The fourth reading is still the actual equation

$$
y-d=f(4)(1+r+k\ell).
\tag{12.13}
$$

First suppose $d\ne0$ and $y\ne d$. Put $e=x-d$. Equation
(12.12) requires $p_5-ek=0$, a polynomial of degree at most two
in $k$. Its quadratic coefficient is $2(d-48)$ and its constant
coefficient is $-3(d-24)/5$. They cannot both vanish, so the
polynomial is not identically zero. It has at most two positive
roots. This includes $d=48$, where $p_5=(72/5)(k-1)$ and the
constraint remains nonzero. Each candidate $k$ uniquely fixes

$$
\ell=\frac{N}{10d k(k+1)}.
\tag{12.14}
$$

In a legal world $y\ne d$ and the positive trace in (12.13) imply
$f(4)\ne0$. Thus

$$
r=\frac{y-d}{f(4)}-1-k\ell
\tag{12.15}
$$

is uniquely fixed. Equations (12.3) and (12.7) then fix the source
and every gain coefficient. There are at most two complete worlds.

Next suppose $d\ne0$ and $y=d$. The same positive trace forces
$f(4)=0$, hence $p_4=0$. Directly from (12.8),

$$
4p_4-3p_5=\frac{(600-9d)k+d-24}{5}.
\tag{12.16}
$$

Since $p_5=ek$, this gives

$$
(600-9d+15e)k+d-24=0.
\tag{12.17}
$$

If $d\ne24$, its nonzero constant permits at most one $k$;
a zero linear coefficient gives no solution. If $d=24$, instead
use $p_4=k(-36k+204/5)$, whose only positive root is $17/15$.
Thus at most one $k$ occurs in either case. It fixes $\ell$ by
(12.14). The remaining rank equation

$$
r(1-r)=(\ell-1)((k-1)\ell+1)
\tag{12.18}
$$

is a nonzero quadratic in $r$, with at most two roots. Each fixes
one complete world by (12.3) and (12.7).

Finally suppose $d=0$. Equation (12.12) becomes

$$
45k^2+k-18=0.
\tag{12.19}
$$

This polynomial is strictly increasing for $k>0$, negative at $3/5$
and positive at $2/3$. It has one positive root $\kappa$, with
$3/5<\kappa<2/3$. Reduction of (12.8) by (12.19) gives

$$
p_4(\kappa,0)=64\kappa-96/5>0,\qquad
p_7(\kappa,0)=(336-392\kappa)/5>0.
\tag{12.20}
$$

Define the positive constants
$c_i=p_i(\kappa,0)/[\kappa(\kappa+1)]$ for $i=4,7$.
Then $f(4)=c_4/\ell$. Set $b=y/c_4-\kappa$; the actual fourth
reading (12.13) gives $r=b\ell-1$. Substituting into (12.18)
gives exactly

$$
(b^2+\kappa-1)\ell^2+(2-\kappa-3b)\ell+1=0.
\tag{12.21}
$$

Its constant is one, so it has at most two real roots, including
all linear or constant degeneracies and repeated roots. Every legal
$\ell$ fixes $r,u,v$ and the entire interpolated gain. Thus there
are at most two worlds even before imposing the fifth reading.

These three cases exhaust $d,y$. In each case retain only candidates
satisfying all positivity and rank conditions and all actual history
equations; filtering cannot increase the count. A polynomial root
alone has not been asserted to give a legal world. No division by
$f(5)$, $x-d$, a leading coefficient or a discriminant occurs.
Interpolation is on the whole cubic-or-lower space and uses no
root-simplicity assumption. ∎

## 13. 末端根层上的分离与八总读完整逆

**引理 13.1（整个实际子纤维上的末端预测对单射）。** On each
$\mathcal C_{x,d}$, the two normalized seventh predictions

$$
R=d+f(7)(k+1)\ell=d+\frac{p_7}{k},\qquad
S=d+f(7)((k+2)\ell-r)
\tag{13.1}
$$

jointly determine the complete world. They are respectively the
seventh-$J$ and seventh-$M$ predictions after the actual fifth and
sixth $J$ readings. No nonzero-terminal-gain premise is required.

Proof. First exclude a world on $H_p$ with
$f(4)=f(6)=f(7)=0$. A nonzero polynomial of degree at most three
with these three distinct roots must be

$$
f(T)=a(T-4)(T-6)(T-7),\qquad a=d/168\ne0,
\tag{13.2}
$$

where the initial reading gives the value of $a$. Put $j=u+v=k\ell$.
The first three noninitial readings in (12.1) imply

$$
j=\frac{28(d-24)}{15d},\qquad
\ell=\frac{21(d-48)}{5d},\qquad
j+\ell=\frac{14(d-312/5)}{d}.
\tag{13.3}
$$

Adding the first two and comparing with the third forces
$d=1344/17$, then $j=13/10$ and $\ell=33/20$. Thus
$u=\ell-1=13/20$ and $v=j-u=13/20$. But
$uv=169/400>1/4$, whereas $r(1-r)\le1/4$, contradicting
(12.18). Lower degrees cannot evade this argument because three
distinct roots already force degree three. Hence the root set
$\{4,6,7\}$ is impossible on this parent.

Consider two worlds in the same $\mathcal C_{x,d}$ with equal
$R,S$. Put $e=x-d$ and $h=R-d$. Another coefficient identity is

$$
3p_5+p_7=\frac{4(72-d)k+d-24}{5}.
\tag{13.4}
$$

By $p_5=ek$ and $p_7=hk$ it gives

$$
3e+h=\frac{4(72-d)}5+\frac{d-24}{5k}.
\tag{13.5}
$$

If $d\ne24$, equality of $x,R,d$ fixes $k$ uniquely, because
$k>0$ and $d-24\ne0$. If $d=24$, the fifth equation alone is
$e=-48k+144/5$, again fixing $k$ without a singular division.

Suppose $d\ne0$. Equation (12.14) now fixes the same $\ell$,
and (12.7) gives the same entire gain for both worlds. If
$f(7)\ne0$, equality of $S$ in (13.1) fixes $r$. If $f(7)=0$,
the preceding exclusion implies $f(4)\ne0$, so the common actual
fourth reading fixes $r$ by (12.15). In either case the complete
worlds agree. This includes the stratum where both terminal
predictions themselves equal $d$.

Suppose instead $d=0$. Lemma 12.3 gives $k=\kappa$,
$r=b\ell-1$ and $f(7)=c_7/\ell$ with $c_7>0$. Consequently

$$
S=c_7\left(\kappa+2-b+\frac1\ell\right).
\tag{13.6}
$$

This is injective in $\ell>1$; for distinct positive
$\ell_1,\ell_2$, the response difference is
$c_7(\ell_2-\ell_1)/(\ell_1\ell_2)\ne0$. Equal $S$ therefore
fixes $\ell$, then $r$ and all of the target. Thus in this case
even $S$ alone is injective. All cases prove the assertion. ∎

**定理 13.2（已知整个根六类的任意子集均有八总读解码）。** For every
$D_0,Y\in\mathbb R$, every $\lambda\ne0$ and every known set
$K\subseteq\mathcal C_6(H_p)$, there is one deterministic policy
recovering the complete target $(P,g,\delta)$ for every member of
$K$ within eight total original-clock readings. The set $K$ has
no cardinality bound and needs neither common drift, symmetric
source, gain-sign restriction nor a nonzero sample at seven.
The policy uses fifth $J$, sixth $J$, and at most one final
seventh action, with singleton early stops permitted.

Proof. The acquired parent already contains the five readings at
clocks $0,1,2,3,4$. Its constants $D_0=z_0$ and
$\lambda=(z_1-z_0)/24$ are available. If the known retained set is
a singleton, return its complete target. Otherwise execute fifth
$J$ and immediately read $z_5$, giving $x$. Stop if its entire
retained child is a singleton. Otherwise execute sixth $J$ and
immediately read $z_6$. The membership premise $f(6)=0$ makes
this actual read $\delta$, so $d=(z_6-D_0)/\lambda$ is now
acquired even when the fifth child had different drifts.

The whole retained set is $K\cap\mathcal C_{x,d}$ and has at
most two complete worlds by Lemma 12.3. Actual membership makes
it nonempty. Return the target if it is a singleton. If it has
two members, evaluate their predictions (13.1) as functions of
these known candidates. Choose seventh $J$ when their $R$ values
differ, and choose seventh $M$ otherwise. In the latter case
Lemma 13.1 guarantees different $S$ values. Thus the chosen one
coordinate is injective on the entire retained set. Execute only
that one atom, immediately read it at clock seven, and return the
unique retained world matching the normalized actual response.
The two alternative predictions are never two acquired readings.

For an explicit inverse description, form the candidates in the
three cases of Lemma 12.3, filter by the full known set and history,
and select the unique candidate matching the last chosen response.
For its $r,k,\ell,d$, return

$$
P=\begin{pmatrix}r&\ell-1\\(k-1)\ell+1&1-r\end{pmatrix},\qquad
g(T)=\lambda\sum_{i=0}^3\alpha_i\ell_i(T),\qquad
\delta=D_0+\lambda d,
\tag{13.7}
$$

where the $\alpha_i$ are (12.7). The rank and positivity filters
and interpolation identify the complete target, not just a source,
gain ray or root label. Existence of an inverse value follows from
the actual legal world; uniqueness is on its entire retained set.

This rule defines one policy for every reachable real response of
the same known $K$, even if $K$ is infinite. Empty children are
unreachable. Actions and inverse functions may be arbitrary
deterministic functions under Definition 1.1; no computability,
efficiency or noise-stability property is asserted. Normalization
and (13.7) are mutually inverse for both signs of $\lambda$.
Every added atom is immediately read on the one unresettable
trajectory. The maximum budget is $5+1+1+1=8$, with clocks exactly
$0,\ldots,7$ and no extra acquisition. ∎

The root-six whole-child bound and its terminal injection are
`repo-derived`. Their mathematical interfaces with preceding results
are the following; standard interpolation and finite-child action
selection are reused inside the proof.

| Mathematical source | Parameter correspondence and scope |
| --- | --- |
| Definitions 1.1–1.2 and (8.3)–(8.5) | The same full target and literal $H_J(Y)$, with $f=g/\lambda$, $d=(\delta-D_0)/\lambda$; the interpolation trace parameters of (8.2) are $u_{8}=k\ell$, $v_{8}=\ell$, $a_{8}=r$. The special fourth and fifth readings of $H_*$ are not imposed. |
| Theorem 5.1 | Its final finite-candidate action selection is reused. It assumes at most two targets in every actual fifth-$M$ fiber. Here the fifth action is $J$, the sixth $J$ acquires drift under (12.2), and Lemma 12.3 proves the bound on each entire resulting child rather than assuming it. |
| Theorem 6.2 | Its common-response, root-six application belongs to the different literal $MMJM$ history (6.1), with additional known $m,j,b,d_6$ conditions. None of those common-response premises is transported to (12.1). |
| [V, Definition 5.1 and Theorem 5.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) | The parent $H_J(Y)$ and $D_0,\lambda,Y$ agree exactly. V assumes $\delta=D_0$ and $g(7)=0$ and uses fifth and sixth $M$. Here only $g(6)=0$ is promised, arbitrary drifts and terminal roots are retained, and fifth and sixth $J$ are actually read. |

## 14. 整个承诺类的排除与不受限原根桥梁

**推论 14.1（整族非 L3 及失败 J 子纤维的非根六成员）。** For every
known $K\subseteq\mathcal C_6(H_p)$,

$$
\neg L_3(K,H_p),\qquad
\neg L_2(K_x,(H_p,J,D_0+\lambda x))\quad\text{for every }x,
\tag{14.1}
$$

where $K_x$ is the entire actual fifth-$J$ response child of $K$.
These conclusions have no finite-cardinality hypothesis.

More generally, let $K\subseteq\mathcal F(H_p)$ be unrestricted
and known. Define its actual children

$$
\begin{aligned}
H_x&=(H_p,J,D_0+\lambda x),&
K_x&=K\cap\mathcal F(H_x),\\
H_{x,w}&=(H_x,J,D_0+\lambda w),&
K_{x,w}&=K\cap\mathcal F(H_{x,w}).
\end{aligned}
\tag{14.2}
$$

Whenever $L_2(K_x,H_x)$, some actual sixth-$J$ response $w$ has
$L_1(K_{x,w},H_{x,w})$, and every such losing sixth child contains
a world with $f(6)\ne0$. For that world $d\ne w$. In particular
$L_3(K,H_p)$ necessarily supplies such a fifth-$J$ child and such
a non-sixth-root member in its losing sixth-$J$ child.

Proof. On a root-six fifth-$J$ child the continuation of Theorem 13.2
uses at most two further readings. Each actual sixth-$J$ response
acquires $d$, after which Lemmas 12.3 and 13.1 give either a
singleton or a pair separated by one chosen last atom. Thus every
whole fifth child is not $L_2$, and the parent is not $L_3$ by
(1.2). This works directly on the entire known set; no triple is
extracted from a larger or infinite losing family.

For unrestricted $K$, recursion (1.2) applied to $L_2(K_x,H_x)$
supplies a losing actual sixth-$J$ response child. If all of its
worlds had $f(6)=0$, (12.5) would give $d=w$ on that whole child,
placing it inside $\mathcal C_{x,w}$. Lemmas 12.3 and 13.1 would
then give a one-read decoder on it, contradicting $L_1$. Hence
it contains a non-sixth-root world. Its positive trace factor in
(12.5) gives $w-d=f(6)(1+r+k\ell)\ne0$. Finally $L_3(K,H_p)$
supplies a losing fifth-$J$ child by the same recursion.

Consequently a losing certificate on the fifth-$M$ arm supported
entirely on sixth-root worlds, even an exact three-world certificate,
cannot by itself be joined into a losing parent consisting only of
sixth-root worlds. The necessary alternate-arm nonroot member need
not be one of those three worlds, and its sixth child need not
contain any sixth-root world. All witnesses must still share the
literal parent (12.1). This conclusion neither realizes nor excludes
a fifth-$M$ losing triple. ∎

**定义 14.2（不受限延伸与原根的未决命题）。** On the unrestricted
parent fiber define

$$
\mathcal U_{x,w}=\mathcal F(H_{x,w}),\qquad
R(W)=d+f(7)(k+1)\ell,\qquad
S(W)=d+f(7)((k+2)\ell-r).
\tag{14.3}
$$

The actual fifth and sixth readings are still (12.5). A sufficient
remaining assertion for the fixed fifth-$J$, sixth-$J$ continuation
is that, for every nonempty $\mathcal U_{x,w}$, at least one of
$R,S$ is injective on that entire fiber. Its last-action obstruction
is one and the same $\mathcal U_{x,w}$ with both

$$
\begin{gathered}
W_1\ne W_2,\quad R(W_1)=R(W_2),\\
W_3\ne W_4,\quad S(W_3)=S(W_4),\qquad
W_1,W_2,W_3,W_4\in\mathcal U_{x,w}.
\end{gathered}
\tag{14.4}
$$

The two pairs may differ or be disjoint. Thus injectivity of a
two-coordinate prediction map, without the proved two-world bound,
would not supply a single lawful last action. Lemmas 12.3 and 13.1
settle this requirement on each known root-six restriction, not on
the unrestricted $\mathcal U_{x,w}$. Constructing or excluding
these mixed-root actual children remains unresolved here. In
particular $H_p$ has not been proved to certify root-six membership,
and a sixth reading on an unrestricted input has not been proved to
reveal its drift. The sixth-root equality is a premise of the decoder.

A result on this unrestricted fixed continuation would still be a
local parent result. The original problem also requires the other
parent actions, other literal histories and every earlier actual
response. A lower-bound tree must supply losing children for both
actions at every required earlier node, consistently retaining the
same complete worlds and ancestors and accounting for early stops.
An original-root decoder must specify lawful actions and complete
answers on all reachable histories. Neither bridge is supplied by
the root-six theorem. The unresolved full-domain alternative is
$n_{\mathrm{det}}(3,0)\ge9$ versus complete-target recovery on all
of $\mathcal W_3$ in at most eight total original-clock readings.
No nine-reading upper bound follows from the conditional decoder.

## 追加锚（本行以下为增补区）

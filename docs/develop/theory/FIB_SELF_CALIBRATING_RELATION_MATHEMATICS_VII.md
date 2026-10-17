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

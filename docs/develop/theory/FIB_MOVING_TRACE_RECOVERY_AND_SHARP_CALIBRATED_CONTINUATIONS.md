# FIB Moving-Trace Recovery and Sharp Calibrated Continuations

## 1. Model, targets, and the scope of sharpness

Fix a declared maximum degree $d\ge1$ and put $m=d+1$. A world is a triple $(P,g,\delta)$ with

$$
P\in\operatorname{Mat}_2(\mathbb R),\qquad P_{ab}>0,\qquad
\operatorname{rank}P=1,\qquad \operatorname{tr}P=1,
$$

$$
g(t)=\sum_{k=0}^d\beta_k t^k,\qquad
\beta\in\mathbb R^{d+1}\setminus\{0\},\qquad \delta\in\mathbb R.
\tag{1.1}
$$

Write $s=\deg g$, so $0\le s\le d$. The declared coefficient space remains all of $\mathbb R^{d+1}$, including when the actual degree drops. Coefficient signs, gain roots at acquisition clocks, repeated roots, and the constant drift are unrestricted.

The atoms, cumulative matrices, and observations are

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad A_0=I,
$$

$$
A_i=E_iA_{i-1},\qquad E_i\in\{M,J\},\qquad
z_i=g(i)\operatorname{tr}(A_iP)+\delta.
\tag{1.2}
$$

There is one trajectory. Each individual action has its immediate read, and the initial read is counted. Thus $N$ total reads occur at original clocks $0,\ldots,N-1$. Chronological words list the actions in the order performed; multiplication in (1.2) is on the left. There are no resets, copies, skipped reads, unread compound actions, inverse acquisition actions, or extra sensors. A deterministic protocol can choose its next action, stopping, and answer from its entire actual history, with no regularity assumption on those choices.

The complete target is the actual normalized triple $(P,g,\delta)$. An unnormalized positive rank-one source $R$ and gain $G$ correspond to this target by

$$
P=R/\operatorname{tr}R,\qquad g=(\operatorname{tr}R)G.
\tag{1.3}
$$

Indeed $g(i)\operatorname{tr}(A_iP)=G(i)\operatorname{tr}(A_iR)$. The unnormalized equivalence $(R,G)\sim(cR,G/c)$ for $c>0$ therefore introduces no remaining equivalence in the normalized target.

A fixed linear gain-ray output on a terminal word $w$ is a fixed matrix $C_w$ such that

$$
C_w(z_0,\ldots,z_{N-1})^{\mathsf T}=\lambda\beta,
\qquad \lambda\ne0.
\tag{1.4}
$$

The matrix entries must not be selected from the observed values. A countable-palette mechanism permits at most countably many preassigned matrices per word and arbitrary history-dependent selection among them. Complete recovery with this mechanism is a more restricted task than unrestricted nonlinear complete recovery. Our upper construction returns exactly $\beta$ with one matrix per terminal word.

A **calibrated continuation at clock $T$** starts after the pure chronological prefix $M^T$, with its entire actual history available and with the actual $g$, $\delta$, and $t_P=\operatorname{tr}(MP)$ known. These are the supplied calibration data; no further information about $P$ is supplied. Here $T\ge0$ is fixed, and the already counted read at clock $T$ is not repeated. Continuation counts refer only to the additional reads after it. Our sharp continuation theorem concerns this problem and the protocols constrained to start with $M^{2d+2}$. It does not give global sharpness for protocols using earlier mixed actions or different calibration.

## 2. Credited pure-$M$ calibration, with its proof

The calibration in this section is Theorem 5.2 of *FIB Linear Gain-Ray Capacity and Hermite Readouts*. Its reuse fixes both the normalized target and the original-clock convention.

**Proposition 2.1 (exact calibration).** The $2d+2$ individual actions $M^{2d+2}$, including the initial read, provide $2d+3$ reads. Fixed linear maps of these reads return the full $\beta$ and $\delta$ exactly. Subsequent processing determines $t_P=\operatorname{tr}(MP)$ on every allowed world.

**Proof.** Put

$$
\phi=\frac{1+\sqrt5}{2},\qquad
\psi=\frac{1-\sqrt5}{2}=-\phi^{-1},\qquad
\Pi_+=\frac{M-\psi I}{\phi-\psi},\qquad
\Pi_-=\frac{\phi I-M}{\phi-\psi}.
\tag{2.1}
$$

The identity $M^2=M+I$ and the two distinct roots $\phi,\psi$ of $x^2-x-1$ give complementary rank-one projectors with

$$
M^i=\phi^i\Pi_++\psi^i\Pi_-,\qquad
\alpha=\operatorname{tr}(\Pi_+P),\qquad
\eta=\operatorname{tr}(\Pi_-P),\qquad \alpha+\eta=1.
\tag{2.2}
$$

For completeness, the projector formulas give their sum $I$, their product zero, and $M\Pi_+=\phi\Pi_+$, $M\Pi_-=\psi\Pi_-$. These identities prove the power formula, including $i=0$. Both projectors have trace one and rank one. The entries of $\Pi_+$ are

$$
\frac1{\phi-\psi}\begin{pmatrix}-\psi&1\\1&1-\psi\end{pmatrix},
$$

all strictly positive, so $\alpha>0$. Nothing forces $\eta$ to be positive: zero and negative values remain in the domain.

Let $D=x\,d/dx$. For a coefficient polynomial $f(x)=\sum_i c_i x^i$,

$$
(D^j f)(\lambda)=\sum_i c_i i^j\lambda^i.
\tag{2.3}
$$

At either nonzero spectral node, the Euler jets through order $d$ are an invertible triangular transform of the ordinary derivative jets: the leading derivative term of $D^j f$ is $x^j f^{(j)}$, and its lower terms have derivative orders less than $j$. The diagonal entries at $\lambda$ are $1,\lambda,\ldots,\lambda^d$, all nonzero.

Prescribing $m$ Euler jets at each of $\phi,\psi$ and a value at $1$ is consequently a nonsingular square system on polynomials of degree at most $2m$. Indeed, a homogeneous solution has roots of multiplicity at least $m$ at both spectral nodes and a root at the third distinct node $1$. It must vanish, because otherwise its degree would be at least $2m+1$. The domain and condition spaces both have dimension $2m+1$, so injectivity proves existence and uniqueness for arbitrary prescribed conditions.

For each $0\le k\le d$, choose its unique polynomials $f_k^+,f_k^-$ with

$$
\begin{aligned}
f_k^+(1)&=0,&(D^j f_k^+)(\phi)&=\delta_{jk},&(D^j f_k^+)(\psi)&=0,\\
f_k^-(1)&=0,&(D^j f_k^-)(\phi)&=0,&(D^j f_k^-)(\psi)&=\delta_{jk}
\end{aligned}
\quad(0\le j\le d),
\tag{2.4}
$$

where $\delta_{jk}$ is the Kronecker symbol. Set $T=2m=2d+2$ and write $f_k^\pm(x)=\sum_{i=0}^T c_{ki}^\pm x^i$. The actual prefix observations satisfy

$$
z_i=\sum_{j=0}^d\beta_j i^j(\alpha\phi^i+\eta\psi^i)+\delta,
\qquad 0\le i\le T.
\tag{2.5}
$$

Substituting (2.5) into the fixed coefficient readouts and using (2.3)--(2.4) gives

$$
U_k=\sum_{i=0}^T c_{ki}^+z_i=\alpha\beta_k,\qquad
V_k=\sum_{i=0}^T c_{ki}^-z_i=\eta\beta_k,
\qquad U+V=\beta.
\tag{2.6}
$$

For the drift, put $Q(x)=x^2-x-1$. The polynomial $f_\delta(x)=(-1)^mQ(x)^m$ has degree $2m$, value $1$ at $1$, and zero Euler jets through order $d$ at both spectral nodes. The same substitution gives

$$
\sum_{i=0}^T [x^i]f_\delta(x)\,z_i=\delta.
\tag{2.7}
$$

Finally choose the least $k$ with $\beta_k\ne0$, which exists, and obtain

$$
\alpha=U_k/\beta_k,\qquad
\eta=1-\alpha,\qquad t_P=\phi\alpha+\psi\eta.
\tag{2.8}
$$

This divides only by a selected nonzero coefficient. There is no division by $\eta$ or any sampled gain. All coefficient polynomials specify weights on the original reads at clocks $0,\ldots,T$; they do not change those clocks. All signs, degree drops, roots, and drifts are included. $\square$

## 3. Every pair of distinct translated powers is useful

Write $K=\operatorname{span}\{I,M\}$. The following statements concern actual acquisition matrices and their algebraic trace reconstruction.

**Lemma 3.1 (pair independence).** Every nonnegative power of $M$ lies in $K$. For every pair of integers $0\le p<q$, the two matrices $M^p,M^q$ form a basis of $K$.

**Proof.** The identity $M^2=M+I$ proves the inclusion of powers by induction; $I$ and $M$ are independent. Suppose $aM^p+bM^q=0$. Apply this equality to a nonzero vector in each spectral eigenspace and divide by the corresponding nonzero $p$-th power. This gives

$$
a+b\phi^{q-p}=0,\qquad a+b\psi^{q-p}=0.
$$

Since $\phi>1$ and $|\psi|=\phi^{-1}<1$, the two powers for the positive exponent $q-p$ are distinct, whether that exponent is even or odd. Hence $b=0$ and then $a=0$. Their independence in the two-dimensional space proves the claim for every pair. $\square$

**Lemma 3.2 (the actual four-matrix basis).** Fix an integer $T\ge0$, and put

$$
C=M^T,\qquad B=JC.
\tag{3.1}
$$

Then $I,M,B,MB$ are a basis of $\operatorname{Mat}_2(\mathbb R)$. For every $0\le p<q$, so are $I,M,M^pB,M^qB$. Thus the four traces against either basis determine every real $2\times2$ matrix uniquely.

**Proof.** First $I,M,J,MJ$ are a basis. A zero linear combination has entries

$$
aI+bM+cJ+eMJ=
\begin{pmatrix}a+e&b+c\\b+c+e&a+b+e\end{pmatrix}=0.
$$

Subtracting the off-diagonal entries gives $e=0$; the first and second diagonal entries then give $a=b=0$, followed by $c=0$.

The matrix $M$ is invertible, with $M^{-1}=M-I$. Both $C$ and $C^{-1}$ belong to the algebra $K$. Right multiplication by $C$ therefore maps $K$ bijectively to itself and maps the displayed four-matrix basis to

$$
C,\quad MC,\quad JC=B,\quad MJC=MB.
$$

Its first two matrices are a basis of $K$, so they can be replaced by $I,M$. This proves the first assertion. Write the unique coordinates

$$
M^r=u_rI+v_rM.
\tag{3.2}
$$

Lemma 3.1 makes the matrix with rows $(u_p,v_p),(u_q,v_q)$ invertible. Multiplying these identities on the right by $B$ gives an invertible change between the last two basis elements $B,MB$ and $M^pB,M^qB$. This proves the second assertion.

If a matrix $S$ has zero trace pairing with every element of either basis, it has zero pairing with every matrix. Pairing with each matrix unit gives every entry of $S$ equal to zero. Thus the trace pairing is nondegenerate and the four trace equations have a unique solution for any data they actually realize. Negative powers here are auxiliary algebra only; no inverse is an acquisition action. $\square$

## 4. Moving-trace complete recovery

**Theorem 4.1 (calibrated continuation).** At any calibrated pure-$M$ state at clock $T\ge0$, the actual source $P$ is recoverable in at most $s+2$ additional immediate reads, where $s=\deg g$. The protocol does not require $s$ to be known in advance.

**Proof and protocol.** With $C=M^T$ and $B=JC$, perform one $J$ and read. Thereafter perform individual $M$ actions and read after every action, stopping as soon as two reads at nonzero gain have occurred in this continuation. Its actual matrices and clocks are

$$
B_r=M^rB,\qquad n_r=T+1+r,\qquad r=0,1,\ldots.
\tag{4.1}
$$

At each read, evaluate the already known polynomial at that same original clock. If $g(n_r)\ne0$, retain

$$
h_r=\frac{z_{n_r}-\delta}{g(n_r)}=\operatorname{tr}(M^rBP).
\tag{4.2}
$$

If $g(n_r)=0$, keep its mandatory read in the history and proceed with one $M$. There is no return action and no division by this zero value.

A nonzero degree-$s$ polynomial has at most $s$ distinct real roots: successively dividing out each distinct linear root factor would otherwise force a divisor of degree greater than $s$. Hence among the $s+2$ distinct continuation clocks $T+1,\ldots,T+s+2$ at least two have nonzero gain. The protocol therefore stops within $s+2$ added actions and their reads. A repeated root contributes one clock to this count; roots in the prefix or at other times do not increase the number of failed continuation clocks.

Let $p<q$ be the actual two retained indices. Their traces satisfy

$$
\begin{pmatrix}h_p\\h_q\end{pmatrix}=
\begin{pmatrix}u_p&v_p\\u_q&v_q\end{pmatrix}
\begin{pmatrix}\operatorname{tr}(BP)\\\operatorname{tr}(MBP)\end{pmatrix}.
\tag{4.3}
$$

Lemma 3.1 proves this coefficient matrix invertible for these actual indices, including every pattern of sampled roots. Solve (4.3), then use Lemma 3.2 and the four values

$$
1,\qquad t_P,\qquad\operatorname{tr}(BP),\qquad\operatorname{tr}(MBP)
\tag{4.4}
$$

to reconstruct $P$. Equivalently one can solve directly against $I,M,M^pB,M^qB$. This reconstruction infers the missing traces algebraically; it does not acquire extra measurements. The actual legal $P$ supplies a solution, and nondegeneracy makes it unique among all real matrices. Consequently the recovered matrix is exactly the actual positive rank-one trace-one source. Together with the known $g,\delta$, it is the complete target. No genericity, sign restriction, or exclusion of $\eta=0$ was used. $\square$

**Theorem 4.2 (uniform and actual-degree bounds).** Every world with declared $d\ge1$ admits complete-target recovery by one deterministic protocol with at most

$$
2d+s+5\le3d+5
\tag{4.5}
$$

total reads. For each terminal word, one fixed matrix returns exactly the full coefficient vector $\beta$.

**Proof.** Execute Proposition 2.1 at $T=2d+2$, costing $T+1=2d+3$ reads. Apply Theorem 4.1, which costs at most $s+2$ more. Adding them proves (4.5), with no reset or repeated initial read. In detail, if the second retained index is $q$, the continuation has $q+1$ actions and reads, the chronological terminal word is $M^TJM^q$, and the total read count is $T+q+2$. The root argument gives $q\le s+1$, as required. For constant nonzero gain the continuation takes exactly the first two reads.

The fixed gain matrix $H_d=(c_{ki}^++c_{ki}^-)_{k,i}$ of (2.6) acts on the prefix only. For a terminal word with $N$ reads, use

$$
C_w=\bigl[\,H_d\ \ 0_{(d+1)\times(N-T-1)}\,\bigr].
\tag{4.6}
$$

It returns exactly $\beta$, so its nonzero scale in (1.4) is $1$. Every possible terminal word has a single preassigned matrix of this form; there are finitely many such words under the uniform bound. Root tests, selection of $p,q$, and nonlinear subsequent reconstruction do not change its entries. Thus complete recovery and the stipulated fixed-linear gain mechanism hold together on the full domain. $\square$

## 5. The entire positive crossing fiber and every scalar obstruction

**Theorem 5.1 (exact $\eta=0$ fiber).** Set

$$
L=\sqrt{1+\phi^2},\qquad
\nu=\frac1L\begin{pmatrix}1\\\phi\end{pmatrix},\qquad
w=\frac1L\begin{pmatrix}-\phi\\1\end{pmatrix},\qquad
\mathcal I=(-\phi,\phi^{-1}).
\tag{5.1}
$$

The entire legal source fiber $\operatorname{tr}(MP)=\phi$, equivalently $\eta=0$, is exactly

$$
\mathcal F=
\{P_x=\nu(\nu+xw)^{\mathsf T}:x\in\mathcal I\}
\ \cup\
\{Q_y=(\nu+yw)\nu^{\mathsf T}:y\in\mathcal I\}.
\tag{5.2}
$$

These are two open line segments intersecting only at the strictly entrywise positive projector $P_*=\nu\nu^{\mathsf T}=\Pi_+$. For every $i\ge0$ and every $P\in\mathcal F$,

$$
\operatorname{tr}(M^iP)=\phi^i.
\tag{5.3}
$$

**Proof.** The vectors $\nu,w$ are orthonormal, with $M\nu=\phi\nu$ and $Mw=\psi w$. In this basis, write an arbitrary real source as $\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$. Trace one and $\operatorname{tr}(MP)=\phi$ give

$$
a+e=1,\qquad \phi a+\psi e=\phi,
$$

so $a=1,e=0$. Rank one is then equivalent to $bc=0$, since the matrix is nonzero and its determinant is $-bc$. If $c=0$ it is $P_b$; if $b=0$ it is $Q_c$. This exhausts the algebraic fiber.

Because both entries of $\nu$ are positive, $P_x$ is strictly entrywise positive exactly when both entries of $\nu+xw$ are positive. These entries are $(1-\phi x)/L$ and $(\phi+x)/L$, giving precisely $-\phi<x<\phi^{-1}$. The same argument gives that interval for $Q_y$. Throughout these intervals the matrices have trace one and rank one. Thus imposing actual strict positivity gives exactly (5.2), without additional branches or endpoints.

If $P_x=Q_y$, then $x\nu w^{\mathsf T}=yw\nu^{\mathsf T}$. Multiplying on the right by $\nu$ gives $y=0$, followed by $x=0$. The intersection is therefore just $P_*$, which is the spectral projector onto the $\phi$ eigenspace. Its entries are all strictly positive. From (2.2), $t_P=\phi\alpha+\psi(1-\alpha)$ equals $\phi$ if and only if $\alpha=1$, equivalently $\eta=0$.

Finally,

$$
\operatorname{tr}(M^iP_x)=(\nu+xw)^{\mathsf T}M^i\nu=\phi^i,
$$

and

$$
\operatorname{tr}(M^iQ_y)=\nu^{\mathsf T}M^i(\nu+yw)=\phi^i.
$$

Here orthogonality eliminates the $w$ component, and symmetry of $M$ permits the second equality. These prove (5.3). $\square$

**Theorem 5.2 (no scalar trace is injective on the crossing fiber).** For every fixed real matrix $A$, the map $P\mapsto\operatorname{tr}(AP)$ fails to be injective on the actual legal fiber $\mathcal F$.

**Proof.** Put

$$
a_A=w^{\mathsf T}A\nu,\qquad b_A=\nu^{\mathsf T}Aw,
\qquad c_A=\operatorname{tr}(AP_*).
$$

The two branches give

$$
\operatorname{tr}(AP_x)=c_A+xa_A,\qquad
\operatorname{tr}(AQ_y)=c_A+yb_A.
\tag{5.4}
$$

If $a_A=0$, any sufficiently small nonzero $x\in\mathcal I$ gives distinct $P_x,P_*$ with equal trace. If $b_A=0$, use distinct $Q_y,P_*$ instead. If both slopes are nonzero, choose a sufficiently small nonzero real $\varepsilon$ and set

$$
x=\varepsilon b_A,\qquad y=\varepsilon a_A.
$$

The open interval $\mathcal I$ contains zero, so both parameters belong to it for sufficiently small $|\varepsilon|$. Both are nonzero and $xa_A=yb_A$. The sources $P_x,Q_y$ are distinct by the intersection assertion of Theorem 5.1, yet (5.4) gives the same scalar trace. All constructed sources are actual strictly positive rank-one trace-one matrices. The argument applies to every $A$, including every cumulative matrix that any legal next action could produce. Arbitrary processing of that one scalar cannot distinguish the exhibited pair. $\square$

## 6. Sharp calibrated continuation and fixed-prefix optimality

**Theorem 6.1 (sharp actual-degree continuation).** Fix $T\ge0$ and an integer $0\le s\le d$. In the calibrated continuation problem over all actual degree-$s$ nonzero gains and all allowed sources and drifts, the optimal uniform bound on additional reads is exactly $s+2$. This lower bound permits arbitrary deterministic adaptive actions, stopping, and nonlinear answers, even when the exact calibration data are supplied without acquisition cost. Consequently for gains of degree at most $d$, the optimal worst-case continuation bound is $d+2$.

**Proof.** Theorem 4.1 proves the upper bound, using the actual known gain without needing its degree in advance. For the lower bound fix a nonzero real $c$, a real drift $\delta_*$, and the single common gain

$$
g_*(\tau)=c\prod_{j=1}^{s}(\tau-(T+j)).
\tag{6.1}
$$

When $s=0$ the product is $1$. This is an allowed polynomial of actual degree exactly $s$. Consider all worlds $(P,g_*,\delta_*)$ with $P\in\mathcal F$. Each is an actual allowed world, and all have $t_P=\phi$.

The entire pure-$M$ prefix histories agree by (5.3): at every original clock $0\le i\le T$ the common observation is $g_*(i)\phi^i+\delta_*$. The supplied values $g_*,\delta_*,t_P$ also agree. Thus the protocol starts its continuation with exactly the same information on this whole family.

At each of the next $s$ clocks $T+1,\ldots,T+s$, the gain is zero. Regardless of the actions selected, the actual observation is $\delta_*$. Induction shows that the actions and histories through these clocks are common to the entire family: the next action is a deterministic function of the previously common information, and its read remains $\delta_*$. A correct protocol cannot stop at any such history, including before the first continuation action, because that history is compatible with distinct complete targets in $\mathcal F$. For $s=0$, this argument simply starts with the common calibrated history and has no intervening root clocks.

Now suppose a correct uniform protocol could finish in at most $s+1$ additional reads. At clock $T+s+1$ its cumulative matrix $A$ is fixed before that last allowed read. The preceding common history fixes this $A$ on the entire family, even though it may depend on the common gain and drift. Theorem 5.2 supplies two distinct $P',P''\in\mathcal F$ with

$$
\operatorname{tr}(AP')=\operatorname{tr}(AP'').
\tag{6.2}
$$

Their read at this last clock is equal by (1.2), as are all earlier reads and calibration data. Their actions, final stopping decision, and answer are then identical. This contradicts correctness for the two different targets.

Selecting the pair after determining $A$ is legitimate: $A$ was fixed by a source-independent history shared by the entire already realized family. Both selected sources realize every preceding action and observation. The pair is therefore a pair of complete legal worlds on one common decision branch, rather than a collision assembled from incompatible histories. No assumption on linearity, countability, continuity, or measurability of the answer was used.

This excludes a uniform bound of $s+1$ or fewer added reads and proves the exact $s+2$ result. Taking $s=d$ supplies the lower bound for the degree-at-most-$d$ problem, while Theorem 4.1 supplies its upper bound $d+2$. $\square$

**Theorem 6.2 (exact pure-$M$-prefix count).** Among deterministic complete-target protocols constrained to start with the fixed chronological prefix $M^{2d+2}$, the optimal uniform total read count on the full degree-at-most-$d$ domain is exactly $3d+5$. More precisely, on the subclass of actual degree $s\le d$, the optimal uniform total count with this prescribed prefix is exactly $2d+s+5$. The lower bounds allow unrestricted nonlinear subsequent processing and impose no gain-output mechanism.

**Proof.** Theorem 4.2 gives one protocol attaining the stated actual-degree and full-domain upper bounds, with an exact fixed-linear gain output as an additional property. For the lower bound set $T=2d+2$ in Theorem 6.1. Its family of degree-$s$ gains and sources shares the entire prescribed prefix. Supplying $g,\delta,t_P$ without cost makes recovery easier; every original protocol is included among the protocols that can ignore these additional supplied data. Hence its impossibility with $s+1$ additional reads also excludes such a bound in the original model. A correct original protocol cannot stop before completing this common pure-$M$ prefix either, since every partial prefix on the same family has distinct compatible targets.

The prefix already costs $T+1$ reads, and the continuation requires at least $s+2$ in the worst case. Thus the exact total is

$$
(T+1)+(s+2)=2d+s+5.
$$

For the full degree-at-most-$d$ domain choose $s=d$ to obtain the matching lower bound $3d+5$. The predetermined prefix is an essential hypothesis of this sharpness statement. $\square$

## 7. Prior results, new contribution, and remaining boundaries

The inherited results used here are those of *FIB Linear Gain-Ray Capacity and Hermite Readouts*, with the following exact correspondence.

| Prior result | Use and scope here |
| --- | --- |
| Definition 1.1 and equations (1.1)--(1.2) | The normalized source, full coefficient space, constant drift, single trajectory, and original immediate-read clock model in Section 1 |
| Lemmas 4.1--4.2 and Theorem 5.2 | The spectral and Hermite calibration reproduced with proof in Proposition 2.1 |
| Theorem 5.3 | The credited exact $2d+3$ gain-only threshold for preassigned acquisition with countable fixed-matrix selection; no adaptive gain-only sharpness is inferred |
| Theorem 3.3 | The credited general complete-protocol lower bound of $2d+3$ under an everywhere successful countable-palette gain-ray mechanism |
| Theorem 7.1 | The valid prior $4d+5$ complete-target upper bound, using returns to two designated mixed states |

Let $N_d^{\mathrm{lin}}$ denote the optimal uniform read bound for deterministic complete-target protocols with an everywhere successful countable fixed-linear gain-ray mechanism. The inherited general lower bound and the present upper bound give

$$
2d+3\le N_d^{\mathrm{lin}}\le3d+5.
\tag{7.1}
$$

The left side is credited to prior Theorem 3.3: pure terminal histories cannot recover the complete source, and its mixed-word universal-identity obstruction together with its countable-cover argument excludes complete protocols through $2d+2$ reads. The countable-cover argument is needed to pass from identities on individual words to arbitrary history-dependent choices of words and matrices. Failure of an all-input palette on each fixed word, without such a joint-cover or target argument, does not alone establish an adaptive lower bound. Equation (7.1) retains exactly the inherited mechanism hypothesis.

The moving-trace improvement and the sharp restricted results correspond to the supplied *Moving-trace and sharpness proofs*, new_theorem_1 through new_theorem_3. Theorems 4.1--4.2 implement the continuing trajectory with the all-pairs and four-matrix proofs of Section 3. Theorems 5.1--5.2 give the entire legal crossing fiber and every scalar obstruction. Theorems 6.1--6.2 supply the common-history root-hiding argument and the precise continuation and prefix quantifiers. Only these proofs and the credited Hermite source are mathematical inputs to this volume; nested references in the supplied proof envelope introduce no additional premises or admitted results.

The gain calibration is prior work, and the earlier $4d+5$ result remains a valid upper bound. The improvement comes from using any two distinct useful matrices $M^pJC,M^qJC$ rather than returning after a failed sample to one prescribed matrix. Every failed root sample then costs just its mandatory action and read. The full crossing fiber explains why two useful scalar source measurements are necessary in the worst calibrated case, and the common gain with consecutive future roots makes that necessity an adaptive continuation obstruction. Spectral decomposition, Hermite interpolation, polynomial root counting, and elementary linear algebra are established tools; the contribution is their application to these acquisition and sharp restricted-recovery statements.

The global sharp complete-target count remains unresolved, both with the countable fixed-linear gain-ray mechanism and without it. The restricted lower bound does not apply to protocols that mix before completing $M^{2d+2}$, use another calibration architecture, or have additional source information. No lower bound for unrestricted nonlinear global complete recovery is deduced from (7.1), and no exact adaptive gain-only threshold is asserted. Earlier unresolved feasibility questions and conditional classifications named by the supplied sources are not settled by the present construction.

All counts concern exact observations in the stated mathematical model. These textual proofs carry no Lean or kernel certification, external-priority or literature-completeness claim, empirical or general-learning conclusion, stability guarantee, or assertion about bit, time, resource, or physical acquisition costs. The broader research programme remains open.

## 追加锚（本行以下为增补区）

## 8. Polynomial drift and the entire calibrated source fiber

**Definition 8.1 (polynomial calibrated continuation).** Fix integers $k,d\ge0$. In Sections 8–12 the source, atoms, cumulative matrices, original consecutive integer clocks, and mandatory immediate reads are those of (1.2), but the observation and complete target are

$$
z_i=H(i)\operatorname{tr}(A_iP)+D(i),\qquad
(P,H,D),\qquad
0\ne H\in\mathbb R[t],\quad \deg H\le k,\quad D\in\Pi_d.
\tag{8.1}
$$

Here $\Pi_d$ is the space of real polynomials of degree at most $d$, including the zero polynomial; $P$ is entrywise strictly positive of rank one and trace one, and $s=\deg H$. There is no bound on the legal coefficients and no restriction on gain signs, degree drops, initial or later roots, or root multiplicities. An unnormalized positive rank-one $R$ with gain $G$ represents this target by $P=R/\operatorname{tr}R$ and $H=(\operatorname{tr}R)G$. Every atom in $\{M,J\}$ has its own next read; the initial read is counted. Resets, copies, empty actions, skipped reads, unread composite actions, and side sensors are unavailable.

At a calibrated state following the actual pure-$M$ prefix through clock $T\ge2$, the exact polynomials $H,D$ and the scalar $b=\operatorname{tr}(MP)>0$ are known. The compatible sources are the entire set

$$
\mathcal F_b=\{P\in\operatorname{Mat}_2(\mathbb R):
P_{ab}>0,\ \operatorname{rank}P=1,\ \operatorname{tr}P=1,
\ \operatorname{tr}(MP)=b\}.
\tag{8.2}
$$

No choice of a representative or further promise about $P$ is supplied. Uniform recovery means correctness for every source in this set, with arbitrary deterministic history-dependent actions, stopping, and nonlinear answers. Additional reads start at $T+1$; the existing read at $T$ is not repeated.

**Proposition 8.2 (the full common-history fiber).** For every $b>0$, $\mathcal F_b$ contains infinitely many actual sources. For fixed $H,D$, all of them have the same entire pure-$M$ history, including every sampled gain root. In particular, neither the calibrated data nor additional pure-$M$ reads distinguish them.

**Proof.** Every positive rank-one trace-one matrix can be written uniquely as

$$
P(r,q)=\frac1{1+rq}
\begin{pmatrix}1&q\\r&rq\end{pmatrix},\qquad r,q>0.
\tag{8.3}
$$

Indeed the row ratio is $r=P_{21}/P_{11}$, the column ratio is $q=P_{12}/P_{11}$, and rank one and trace one give the displayed formula. Its $M$ trace is $b$ exactly when

$$
r+q+rq=b(1+rq).
\tag{8.4}
$$

For all sufficiently small $r>0$, set

$$
q=\frac{b-r}{1-(b-1)r}>0.
\tag{8.5}
$$

This gives (8.4), and different $r$ give different sources. Finally $M^2=M+I$ implies

$$
\operatorname{tr}(M^iP)=f_i+F_i b\quad(i\ge0),
\qquad f_0=1,\quad f_i=F_{i-1}\ (i\ge1).
\tag{8.6}
$$

The two initial values are $1,b$, and both sides obey the same recurrence. Substitution into (8.1) proves equality of every pure-$M$ observation, without dividing by any gain. Conversely every source compatible with the known $b$ satisfies (8.2), so no other source information is implicit in this history. $\square$

## 9. Exact whole-fiber classification of the first mixed trace

**Theorem 9.1 (closed exterior sectors and interior collisions).** For every integer $T\ge2$, let

$$
L_T=\min\left\{\frac{F_T}{F_{T-1}},\frac{F_{T+1}}{F_T}\right\},
\qquad
U_T=\max\left\{\frac{F_T}{F_{T-1}},\frac{F_{T+1}}{F_T}\right\}.
\tag{9.1}
$$

For every $b>0$, the map

$$
P\longmapsto\operatorname{tr}(JM^TP)
\tag{9.2}
$$

is injective on the entire $\mathcal F_b$ if and only if $b\notin(L_T,U_T)$. Both equality endpoints are injective. For every interior $b$ there exist distinct strictly positive actual sources in $\mathcal F_b$ with equal (9.2), hence with the same entire pure-$M$ history and the same next $J$ observation for every common $H,D$. The value $b=\phi$ lies strictly in this interior for every finite $T\ge2$.

**Proof.** Put

$$
a=F_{T-1},\qquad c=F_T,\qquad \rho=a/c>0.
$$

Induction using the Fibonacci recurrence gives

$$
M^T=\begin{pmatrix}a&c\\c&a+c\end{pmatrix},\qquad
JM^T=\begin{pmatrix}c&a+c\\a&c\end{pmatrix}.
\tag{9.3}
$$

Write $P=\left(\begin{smallmatrix}1-t&u\\v&t\end{smallmatrix}\right)$. The trace and $M$ trace conditions give $u+v+t=b$, while

$$
\operatorname{tr}(JM^TP)=c+au+(a+c)v.
\tag{9.4}
$$

Consequently two distinct sources with the same $b$ and (9.2) differ by a nonzero multiple of

$$
K_\rho=\begin{pmatrix}-1&-(1+\rho)\\\rho&1\end{pmatrix}.
\tag{9.5}
$$

Interchange their names so that $Q-P=hK_\rho$ with $h>0$. Write the positive rank-one matrices as

$$
P=\begin{pmatrix}p&q\\xp&xq\end{pmatrix},\qquad
Q=\begin{pmatrix}p'&q'\\yp'&yq'\end{pmatrix}.
$$

Since $p'=p-h>0$ and $yp'=xp+h\rho$, one has $y>x>0$. The two column equations now give

$$
(y-x)p=h(y+\rho),\qquad
(y-x)q=h((1+\rho)y+1).
$$

Define

$$
\Delta=(1+\rho)xy+x+y+\rho>0.
$$

The trace-one condition gives $h=(y-x)/\Delta$. Thus every colliding pair has exactly the form

$$
\begin{aligned}
P_{x,y}&=\frac1\Delta
\begin{pmatrix}
y+\rho&(1+\rho)y+1\\
x(y+\rho)&x((1+\rho)y+1)
\end{pmatrix},\\
Q_{x,y}&=\frac1\Delta
\begin{pmatrix}
x+\rho&(1+\rho)x+1\\
y(x+\rho)&y((1+\rho)x+1)
\end{pmatrix},\qquad 0<x<y.
\end{aligned}
\tag{9.6}
$$

Conversely (9.6) gives two strictly positive rank-one trace-one matrices, whose difference is $(y-x)K_\rho/\Delta$. They are distinct, their mixed traces agree, and their common $M$ trace is

$$
b(x,y)=\frac{(2+\rho)xy+(1+\rho)(x+y)+1}
{(1+\rho)xy+(x+y)+\rho}.
\tag{9.7}
$$

This quotient is a weighted average, with strictly positive weights $(1+\rho)xy$, $x+y$, and $\rho$, of

$$
\frac{2+\rho}{1+\rho},\qquad 1+\rho,\qquad \frac1\rho.
\tag{9.8}
$$

The first number lies strictly between the last two. In fact

$$
\frac{2+\rho}{1+\rho}-\frac1\rho
=\frac{\rho^2+\rho-1}{\rho(1+\rho)},\qquad
\frac{2+\rho}{1+\rho}-(1+\rho)
=-\frac{\rho^2+\rho-1}{1+\rho}.
\tag{9.9}
$$

Here $\rho^2+\rho-1\ne0$, since $\rho$ is rational and its positive root is $\phi^{-1}$. Hence (9.7) lies strictly between $1/\rho$ and $1+\rho$, which are precisely the two endpoints in (9.1). This proves absence of collisions everywhere outside the open interval, including at both endpoints; strict positivity of all weights is essential at the endpoints.

For existence at every interior $b$, set

$$
y(x)=\frac{1-b\rho+(1+\rho-b)x}
{b-1-\rho+\bigl(b(1+\rho)-(2+\rho)\bigr)x}.
\tag{9.10}
$$

Because $b$ is strictly between $1/\rho$ and $1+\rho$, both $1-b\rho$ and $b-1-\rho$ are nonzero and have the same sign. Thus $y(x)$ is defined near zero and tends to

$$
y(0)=\frac{1-b\rho}{b-1-\rho}>0.
$$

Choose any sufficiently small $x>0$ so that $y(x)>x$. Equation (9.10), multiplied by its nonzero denominator, is exactly $b(x,y(x))=b$. The pair (9.6) therefore realizes the desired collision by actual strictly positive sources, without a limiting or zero-entry source. Proposition 8.2 gives their common pure-$M$ history, and multiplying their equal mixed traces by the same next gain and adding the same drift preserves equality.

Finally

$$
1+\rho-\phi=\rho-\phi^{-1},\qquad
\rho^{-1}-\phi=-\frac\phi\rho(\rho-\phi^{-1}).
$$

Their product is strictly negative, again by irrationality of $\phi^{-1}$. Thus $\phi$ is strictly between the endpoints, and (9.6)–(9.10) apply to it as well. $\square$

**Corollary 9.2 (an explicit exterior inverse and a singleton interior response).** On either closed exterior sector of Theorem 9.1, a realized value $\lambda=\operatorname{tr}(JM^TP)$ determines $P$ by the following quadratic inverse. Set $c=F_T$ and $\rho=F_{T-1}/F_T$, and put

$$
w=\lambda/c-1-\rho b.
$$

There is exactly one real root $t$ of

$$
(\rho^2+\rho-1)t^2+
\bigl(1-\rho b+(1+2\rho)w\bigr)t+w^2-bw=0
\tag{9.11}
$$

that satisfies $0<t<1$, $v=w+\rho t>0$, and $u=b-t-v>0$. It returns $P=\left(\begin{smallmatrix}1-t&u\\v&t\end{smallmatrix}\right)$. Failure of whole-fiber injectivity in the interior does not imply that every individual response fiber collides: at $b=\phi$ the response of $P_* =\nu\nu^{\mathsf T}$ from Theorem 5.1 has a singleton fiber for (9.2).

**Proof.** Equations (9.4) and $u+v+t=b$ give $v-\rho t=w$. Substitution into $t(1-t)=uv$ gives (9.11). The stated inequalities give strict positivity and the equation gives rank one. The actual source proves existence, and Theorem 9.1 proves uniqueness among these admissible roots. The coefficient $\rho^2+\rho-1$ is nonzero, but no lower bound on it is needed for exact inversion.

For the singleton assertion, Theorem 5.1 exhausts $\mathcal F_\phi$ by $P_x,Q_y$ with their common point $P_*$. In (5.4) for $A=JM^T$, its two slopes are

$$
a_A=\phi^T\gamma,\qquad b_A=\psi^T\gamma,\qquad
\gamma=w_0^{\mathsf T}J\nu=-\frac\phi{1+\phi^2}\ne0,
$$

where $w_0=(-\phi,1)^{\mathsf T}/\sqrt{1+\phi^2}$ denotes the vector called $w$ in (5.1). Both slopes are nonzero. On either branch only its zero parameter gives the response of $P_*$, and those zero parameters give the same source. $\square$

## 10. The exact one-additional-read criterion

**Theorem 10.1 (uniform one-read recovery).** At any calibrated state of Definition 8.1, for fixed known $H,D,b$, a deterministic protocol recovering the complete target uniformly on the entire $\mathcal F_b$ with at most one additional read exists if and only if

$$
H(T+1)\ne0\qquad\hbox{and}\qquad b\notin(L_T,U_T).
\tag{10.1}
$$

This equivalence allows arbitrary adaptive or nonlinear protocols and uses no restriction on the gain or drift beyond Definition 8.1.

**Proof.** If (10.1) holds, perform $J$ at the next clock, retain its mandatory observation, and compute

$$
\lambda=\frac{z_{T+1}-D(T+1)}{H(T+1)}.
$$

Theorem 9.1, or the explicit inverse (9.11), recovers the unique actual $P$. Together with the known $H,D$ this is the complete target.

For necessity, Proposition 8.2 shows that the complete calibrated histories coincide on an infinite family of sources, so a uniformly correct protocol cannot stop without another read. Its next action is fixed on this common history. If $H(T+1)=0$, either action returns just $D(T+1)$ on every source, so recovery is impossible. If the action is $M$, (8.6) makes its read independent of the source within $\mathcal F_b$, even at nonzero gain. The only remaining action is $J$ with nonzero gain. For every interior $b$, Theorem 9.1 supplies a pair of distinct actual sources with identical new response and the same previous history. The protocol has the same action, stopping decision, and answer on that pair, and cannot be correct on both. Processing the response by an arbitrary nonlinear rule cannot remove equality of the input histories. This proves necessity without any regularity assumption on the protocol. The statement is uniform; Corollary 9.2 explains why it is not a claim about every individual interior response. $\square$

## 11. Exact exterior continuation budgets

**Theorem 11.1 (root wait and sharp exterior uniform budgets).** Fix $T\ge2$ and any $b>0$ with $b\notin(L_T,U_T)$. For a particular known nonzero polynomial $H$ define

$$
\tau_T(H)=\min\{j\ge1:H(T+j)\ne0\}.
\tag{11.1}
$$

For every fixed known $D$, the optimal number of additional reads sufficient uniformly for all $P\in\mathcal F_b$ is exactly $\tau_T(H)$. Over all actual degree-$s$ gains, the optimal uniform additional-read budget is exactly $s+1$. Over the nonzero gains of degree at most $k$ it is exactly $k+1$. These sharp statements retain the atomic immediate-read contract and allow arbitrary deterministic adaptive and nonlinear competitors.

**Proof.** First the exterior condition persists through every later pure-$M$ clock. Put $r_n=F_{n+1}/F_n$ for $n\ge1$. For $n\ge2$,

$$
r_{n+1}=\frac{F_n r_n+F_{n-1}r_{n-1}}{F_n+F_{n-1}}.
\tag{11.2}
$$

The consecutive ratios are distinct: the determinants $F_{n+1}F_{n-1}-F_n^2$ alternate sign from the initial value $1$ at $n=2$, by the Fibonacci recurrence. Thus (11.2) is strictly between its two terms. Each interval $(L_{S+1},U_{S+1})$ is contained in $(L_S,U_S)$ for $S\ge2$. Induction gives

$$
b\notin(L_T,U_T)\ \Longrightarrow\
b\notin(L_S,U_S)\quad\hbox{for every }S\ge T.
\tag{11.3}
$$

A nonzero degree-$s$ polynomial has at most $s$ distinct roots, so $\tau=\tau_T(H)$ exists and $\tau\le s+1$. Perform individual $M$ actions, with every immediate read, at the clocks $T+1,\ldots,T+\tau-1$. These are all gain roots. Then perform $J$ and read at clock $T+\tau$. Before that last action the actual state is still the pure prefix $M^S$ with $S=T+\tau-1$. The known calibration data have not changed, (11.3) gives the exterior condition at $S$, and the gain at $S+1$ is nonzero. Theorem 10.1 therefore recovers $P$ in this last read. There are exactly $\tau$ new actions and reads, including every root clock; the wait has no empty or unread action.

For the lower bound with this particular $H$, fix any two distinct sources in $\mathcal F_b$ before the continuation starts. Such a pair exists by Proposition 8.2. They share the entire prefix and supplied calibration data. At each of the first $\tau-1$ additional clocks the gain is zero, independently of which actions are chosen. Its response is $D$ at that same original clock. Induction on these clocks makes all actions and actual histories common to this fixed pair. A correct deterministic protocol cannot stop at any of those histories because the targets differ. Thus it needs at least $\tau$ reads in the worst case. This proves the exact fixed-$H$ root wait.

For sharpness uniformly over all actual degree-$s$ gains, fix before any adaptive choices the two sources just described, any $D_*$ in the allowed drift space, and the single common gain

$$
H_*(t)=c_*\prod_{j=1}^{s}(t-(T+j)),\qquad c_*\in\mathbb R\setminus\{0\}.
\tag{11.4}
$$

The empty product for $s=0$ is $1$. These are two complete fixed legal worlds of actual degree $s$, sharing their entire pure-$M$ prefix and the same known $H_*,D_*,b$. Their first $s$ future gains are zero. Whatever deterministic adaptive actions are chosen, induction keeps their histories equal through all these reads, so no uniform protocol can finish within $s$ reads. All worlds and coefficients in this argument were fixed before the adaptive actions, with no response-dependent source selection. The upper bound already proved is $s+1$, so it is exact. Taking $s=k$ proves the lower bound for degree at most $k$, and root counting gives its matching upper bound. Negative $c_*$ is equally legal. Earlier roots and repeated roots in a general known $H$ affect (11.1) only when they occur at those distinct future integer clocks. $\square$

## 12. Paid calibration and the exterior consumer

**Theorem 12.1 (paid polynomial calibration with a sharper exterior branch).** In the full model (8.1), put

$$
N=2k+d+3,\qquad T=N-1.
\tag{12.1}
$$

There is a single deterministic complete-target protocol starting with the paid pure-$M$ prefix through $T$ which has the following total-read bounds, where $s=\deg H$:

$$
\begin{cases}
N+s+1=2k+d+s+4\le3k+d+4,
& b\notin(L_T,U_T),\\
N+s+2=2k+d+s+5\le3k+d+5,
& b\in(L_T,U_T).
\end{cases}
\tag{12.2}
$$

In particular the global $3k+d+5$ guarantee is preserved, while the whole closed exterior branch saves one read in its actual-degree and degree-at-most-$k$ guarantees. These are bounds for the stated paid-prefix architecture; no unrestricted global optimum or optimum for an earlier-mixing architecture is asserted.

**Proof.** Apply the prefix part of Theorem 39.2 of [*FIB Self-Calibrating Relation Mathematics*](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#39-任意已知有限次共同增益的零安全固定历史恢复), with its normalized $R_0$ identified with the present $P$. Its already established linear inverse on the first $N$ reads returns the same actual $H,D,b$ used in Definition 8.1. In that theorem the auxiliary coefficient polynomials are $H$ and $bH$; selecting a nonzero coefficient of $H$ determines $b$, without division by a sampled gain. The known-node confluent interpolation ingredient is the one credited there to Batenkov–Yomdin, §2B, [arXiv:1106.1137v3](https://arxiv.org/abs/1106.1137v3). No separate calibration is needed here, and all $N$ prefix reads, including the initial read, are paid. Since $k,d\ge0$, this $T$ is at least $2$.

Test the now known scalar $b$ against (9.1). On the exterior branch apply Theorem 11.1 to the same actual source and original clock. Its cost is $\tau_T(H)\le s+1$. Adding the paid $N$ gives the first line of (12.2).

On the interior branch use precisely the existing moving-trace decoder of Theorem 4.1: perform $J$ once and thereafter individual $M$ actions, retaining the first two reads with nonzero gain. The only change to its observation formula (4.2) is the subtraction of the already known polynomial drift at the actual clock:

$$
h_r=\frac{z_{T+1+r}-D(T+1+r)}{H(T+1+r)}
=\operatorname{tr}(M^rJM^TP),\qquad H(T+1+r)\ne0.
\tag{12.3}
$$

Every zero-gain clock still has its mandatory action and read. Among $s+2$ consecutive clocks two are nonroots, and Lemmas 3.1–3.2 give exactly the same four-trace inverse from those actual two indices and the known $1,b$. Thus the existing decoder returns this same $P$ within $s+2$ additional reads. Known $H,D$ complete the target. Polynomial drift of any allowed degree, including zero drift, has no further role after its pointwise subtraction. Adding $N$ gives the second line of (12.2).

All gain signs, initial roots, later roots, repeated roots, degree drops, and unbounded legal coefficients remain in the argument. Every trace used by either decoder comes from the same fixed source and one continuing legal trajectory. $\square$

## 追加锚（本行以下为增补区）

## 13. Exact continuation interface and the inherited integer bound

**Definition 13.1 (the calibrated optimization problem).** Fix independent integers $k,d\ge0$, an original clock $T\ge2$, and a scalar $b>0$. Throughout Sections 13–19,

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\qquad A_i=E_iA_{i-1},\quad E_i\in\{M,J\},
$$

$$
z_i=H(i)\operatorname{tr}(A_iP)+D(i),\qquad
0\ne H\in\mathbb R[t],\quad \deg H\le k,\quad D\in\Pi_d,
\tag{13.1}
$$

where $\Pi_d$ includes zero and $P$ is strictly entrywise positive, rank one, and trace one. The actual prefix is $A_i=M^i$ through clock $T$. The exact $H,D,b=\operatorname{tr}(MP)$ are supplied, and the compatible source set is the entire $\mathcal F_b$ of (8.2), with no representative or further source promise. All coefficient signs and magnitudes, degree drops, roots at any clock, and repeated roots are retained. The target is the actual normalized triple $(P,H,D)$.

There is one trajectory. Every atom has its mandatory immediate read at the next consecutive original integer clock, and the initial read is counted. There is no reset, copy, empty action, skipped read, clock jump, unread composite action, inverse acquisition, or side sensor. A chronological word of length $n$ means exactly $n$ individually performed atoms and $n$ additional reads, even if its matrix admits cancellations. Competitors may choose actions, stopping, and nonlinear answers by arbitrary deterministic functions of their whole actual histories; no regularity assumption is imposed.

Write $I_S=(L_S,U_S)$ for (9.1), $S\ge2$, with $F_0=0,F_1=1$. Let $C_T(b;H,D)$ be the minimum uniform additional-read bound among protocols correct for every $P\in\mathcal F_b$ at this calibrated state. This is a worst case over the whole source fiber, with the particular $H,D,b,T$ fixed. It does not assert a minimum for each individual source or for an uncalibrated acquisition problem.

**Lemma 13.2 (off-diagonal difference at literal cost).** If $A=E_m\cdots E_1$ is any literal word of length $m\ge3$, and $A=(a_{ij})$, then

$$
|a_{12}-a_{21}|\le F_{m-1}.
\tag{13.2}
$$

**Proof.** Reuse the signed bound $-(W_{22}-W_{11})\le F_{\ell-2}$ for every literal word $W$ of length $\ell\ge3$, from Lemma 25.1 of [*FIB Self-Calibrating Relation Mathematics*](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#25-fibonacci-系数与两个受限稳定性最优区). Its existing Lean source declaration is `raw_word_fibonacci_bounds` in `D5/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds.lean`. No induction for that bound is needed here. Both $JA$ and $AJ$ are literal words of length $m+1$, and

$$
(JA)_{22}-(JA)_{11}=a_{12}-a_{21},\qquad
(AJ)_{22}-(AJ)_{11}=a_{21}-a_{12}.
$$

Applying the inherited signed bound to both words proves (13.2). These two words are algebraic inputs to a universal word inequality, not additional acquisitions. In particular, no permission to prepend an action to the actual trajectory is used. $\square$

**Lemma 13.3 (the denominator gap).** For $S\ge2$, put

$$
u_S=\frac{F_{S-2}}{F_{S-1}},\qquad
v_S=\frac{F_{S-1}}{F_S},\qquad
K_b=\left[\min\{b-1,b^{-1}\},\max\{b-1,b^{-1}\}\right].
\tag{13.3}
$$

If $b\in I_S$, then $1<b<2$, and $K_b$ lies strictly between $u_S$ and $v_S$. Every rational in $K_b$, in reduced form with positive denominator $q$, satisfies

$$
q\ge F_{S-1}+F_S=F_{S+1}>F_S.
\tag{13.4}
$$

**Proof.** The nesting established in (11.2)–(11.3) gives $I_S\subseteq I_2=(1,2)$. The endpoints defining $I_S$ are exactly $1+u_S$ and $1+v_S$, so $b-1$ is strictly between $u_S,v_S$. The reciprocal map $x\mapsto1/(1+x)$ sends $u_S$ to $v_S$ and $v_S$ to

$$
\frac{F_S}{F_{S+1}}
=\frac{F_{S-2}+F_{S-1}}{F_{S-1}+F_S},
$$

the strict mediant of the two distinct fractions $u_S,v_S$. Thus $1/b$ also lies strictly between them, as does the whole closed segment $K_b$.

Cassini's determinant identity from the Fibonacci recurrence gives

$$
\left|F_{S-2}F_S-F_{S-1}^2\right|=1.
$$

For completeness, if $a/c<p/q<a'/c'$ with positive denominators and $a'c-ac'=1$, the positive integers

$$
x=a'q-c'p,\qquad y=cp-aq
$$

satisfy $q=cx+c'y\ge c+c'$. Applying this to the two fractions $u_S,v_S$ in increasing order proves (13.4), including $S=2$ with neighbors $0/1,1/1$. This is the elementary Farey-neighbor denominator fact; the determinant and mediant setting agrees with [MathWorld, *Farey Sequence*, equations (6)–(9)](https://mathworld.wolfram.com/FareySequence.html). Its only use here is this integer inequality, whose proof does not assume an acquisition model. $\square$

## 14. Scalar collision directions on the whole positive fiber

**Lemma 14.1 (necessary directions for an injective scalar).** Fix $1<b<2$ and a real matrix

$$
A=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix},\qquad
 e=\beta-\gamma,\qquad f=\delta-\alpha-\gamma.
$$

If $P\mapsto\operatorname{tr}(AP)$ is injective on the entire $\mathcal F_b$, then $e\ne0$ and, with $\rho=-f/e$, at least one of

$$
\rho\in K_b,\qquad -1-\rho\in K_b
\tag{14.1}
$$

holds. Every collision used to prove this necessity consists of two distinct strictly positive rank-one trace-one matrices with the same prescribed $b$.

**Proof.** Write $P=\left(\begin{smallmatrix}1-t&u\\v&t\end{smallmatrix}\right)$. On $\mathcal F_b$, $u+v+t=b$, and hence

$$
\operatorname{tr}(AP)=\alpha+\gamma b+ft+ev.
\tag{14.2}
$$

If $e=0$, a nonsymmetric $P$ and its transpose have equal (14.2). Such sources exist for every $b>0$: in (8.3)–(8.5) take $r>0$ sufficiently small, so $q\to b>0$ while $r\to0$. Then $P\ne P^{\mathsf T}$ and both belong to $\mathcal F_b$. This proves noninjectivity when $e=0$.

Suppose $e\ne0$. Equal responses are equivalent to equal values of $v-\rho t$. Reuse the algebraic pair (9.6): for a real $\rho$ and $0<x<y$, put

$$
\Delta=(1+\rho)xy+x+y+\rho,
$$

$$
\begin{aligned}
P_{x,y}&=\frac1\Delta
\begin{pmatrix}y+\rho&(1+\rho)y+1\\x(y+\rho)&x((1+\rho)y+1)\end{pmatrix},\\
Q_{x,y}&=\frac1\Delta
\begin{pmatrix}x+\rho&(1+\rho)x+1\\y(x+\rho)&y((1+\rho)x+1)\end{pmatrix}.
\end{aligned}
\tag{14.3}
$$

Whenever all the displayed entries are positive, these are rank-one trace-one sources, and

$$
Q_{x,y}-P_{x,y}=\frac{y-x}{\Delta}
\begin{pmatrix}-1&-(1+\rho)\\\rho&1\end{pmatrix}.
\tag{14.4}
$$

Their common $M$ trace is the quotient (9.7). Requiring this quotient to equal $b$ gives exactly

$$
y(x)=\frac{1-b\rho+(1+\rho-b)x}
{b-1-\rho+\bigl(b(1+\rho)-(2+\rho)\bigr)x}.
\tag{14.5}
$$

For $\rho>0$ outside $K_b$, $b$ lies strictly between $1+\rho$ and $1/\rho$. Consequently $1-b\rho$ and $b-1-\rho$ are nonzero with the same sign, so $y(0)>0$. Take $x>0$ sufficiently small that (14.5) is defined and $y(x)>x$. All entries and $\Delta$ in (14.3) are then strictly positive. Equations (14.4)–(14.5) give two distinct actual sources in $\mathcal F_b$ with equal response. This is precisely the positive-direction collision construction underlying Theorem 9.1, with its parameter left free.

For $-1\le\rho\le0$, set $x_0=-\rho$ and $y_0=1/(b-1)>1\ge x_0$. Let $c_\rho=1-\rho-\rho^2>0$. The denominator in (14.5) at $x_0$ is $(b-1)c_\rho>0$, and $y(x_0)=y_0$. Also $\Delta(x_0,y_0)=c_\rho y_0>0$. Take $x>x_0$ sufficiently close to $x_0$. Then $0<x<y(x)$, $x+\rho>0$, $y(x)+\rho>0$, and both $(1+\rho)x+1$ and $(1+\rho)y(x)+1$ are positive. Thus (14.3) again supplies a strictly positive distinct colliding pair with exactly this $b$. The limiting zero entry at $x=x_0$ is not used as a source; the chosen $x>x_0$ is essential.

Finally transposition preserves $\mathcal F_b$ and sends the direction $\rho$ to $\rho'=-1-\rho$, since

$$
(v-\rho t)(P^{\mathsf T})=u-\rho t
=b-\bigl(v-\rho't\bigr)(P).
$$

If $\rho<-1$, then $\rho'>0$, and the positive-direction construction applies unless $\rho'\in K_b$. These cases exhaust all real $\rho$ and establish (14.1). The lemma asserts a necessary condition, which is all that the word lower bound needs. $\square$

## 15. A universal exact-length acquisition bridge

**Theorem 15.1 (all literal continuations and an attained terminal trace).** For every $T\ge2$, $n\ge1$, and $b>0$, there exists an actual $n$-atom continuation of the prefix $M^T$ whose terminal scalar trace is injective on the whole $\mathcal F_b$ if and only if

$$
b\notin I_{T+n-1}.
\tag{15.1}
$$

Both interval endpoints belong to the injective side. If $b\in I_{T+n-1}$, every permitted literal $n$-atom continuation has a terminal trace collision between two distinct actual sources in $\mathcal F_b$, including continuations whose matrices contain cancellations.

**Proof.** Put $S=T+n-1$. If $b\notin I_S$, perform $n-1$ individual $M$ actions and then one $J$. Its terminal matrix is $JM^S$, and Theorem 9.1 proves whole-fiber injectivity, including equality at either endpoint. The word has exactly $n$ actions and reads; it is not an arbitrary selected matrix or an unread composite.

For necessity, fix any literal $n$-atom continuation. Its terminal matrix $A=E_n\cdots E_1M^T$ is an integer matrix of literal length $m=T+n=S+1$. Suppose $b\in I_S$ and its scalar were injective. Lemma 14.1 applies because $1<b<2$. With its notation, $e\ne0$ is an integer, and Lemma 13.2 gives $|e|\le F_S$. Each of $\rho=-f/e$ and $-1-\rho$ is rational with reduced positive denominator at most $|e|$. By Lemma 14.1 one lies in $K_b$, whereas Lemma 13.3 says every rational there has denominator greater than $F_S$. This contradiction excludes injectivity for the arbitrarily fixed word. For $e=0$, the explicit transpose collision in Lemma 14.1 already excludes it.

The inherited word inequality uses the literal length, so no reduction of a word containing $JJ$ or any other cancellation escapes the argument. This theorem concerns the terminal scalar alone. Earlier nonzero-gain observations may carry additional information; the next theorem uses the root pattern to specify exactly when the terminal-scalar obstruction becomes a whole-history lower bound. $\square$

## 16. The first two nonroot clocks determine the exact optimum

**Theorem 16.1 (exact fixed-gain calibrated continuation).** For any particular known $H\ne0$ and known $D$ in (13.1), let $r_1<r_2$ be the first two positive integer offsets $j$ with $H(T+j)\ne0$. Then

$$
C_T(b;H,D)=
\begin{cases}
r_1,&b\notin I_{T+r_1-1},\\
r_2,&b\in I_{T+r_1-1}.
\end{cases}
\tag{16.1}
$$

This minimum is attained by legal atomic continuations. Its lower bound holds against all the deterministic adaptive competitors of Definition 13.1, with two fixed complete legal worlds on a common actual history whenever a collision is needed.

**Proof of attainment.** A nonzero polynomial has finitely many distinct roots, so $r_1,r_2$ exist. On the first branch of (16.1), perform $M$ separately at offsets $1,\ldots,r_1-1$ and $J$ at offset $r_1$, reading immediately after every action. All the former clocks are gain roots. With $S=T+r_1-1$, the terminal matrix is $JM^S$ and

$$
\lambda=\frac{z_{T+r_1}-D(T+r_1)}{H(T+r_1)}
=\operatorname{tr}(JM^SP).
\tag{16.2}
$$

Theorem 9.1 and the admissible positive-root inverse of Corollary 9.2 recover the unique actual $P$. Only this nonzero gain is divided by. Known $H,D$ complete the target, at exactly $r_1$ additional reads.

On the second branch perform $J$ at offset $1$, then individual $M$ actions through offset $r_2$, retaining every mandatory read. At each of the two nonroot offsets $j\in\{r_1,r_2\}$ retain

$$
h_j=\frac{z_{T+j}-D(T+j)}{H(T+j)}
=\operatorname{tr}(M^{j-1}JM^TP).
\tag{16.3}
$$

By Lemmas 3.1–3.2, the matrices

$$
I,\quad M,\quad M^{r_1-1}JM^T,\quad M^{r_2-1}JM^T
$$

form a basis of all real $2\times2$ matrices. Solve the four trace equations with right sides $1,b,h_{r_1},h_{r_2}$, equivalently the two-step inverse (4.3)–(4.4). The actual source supplies a solution and the nondegenerate trace pairing makes it unique. This is the existing moving-trace decoder with $D$ subtracted at the actual original clocks. It recovers exactly $P$ in $r_2$ additional reads, even if the first $J$ occurs at a gain root. Every intervening root clock still executes its specified paid atom and takes its read.

**Proof of the adaptive lower bound.** Fix any correct deterministic competitor and the particular $H,D,b,T$. Proposition 8.2 gives a common entire pure-$M$ prefix and common supplied calibration data on all of $\mathcal F_b$. Through offsets $1,\ldots,r_1-1$, each observation is the fixed value $D(T+j)$ whatever atom is selected. Induction therefore makes all selected actions and histories common to the entire fiber. A correct competitor cannot stop there, since this infinite fiber contains different complete targets. Thus at least $r_1$ reads are necessary on either branch.

Suppose now that $b\in I_{T+r_1-1}$. The common history just proved fixes the entire literal word through offset $r_1$ before its nonzero-gain response is received. Theorem 15.1 applies to this particular word and supplies distinct $P',P''\in\mathcal F_b$ with equal terminal scalar trace. The two complete worlds $(P',H,D)$ and $(P'',H,D)$ have equal observations through offset $r_1$, including its nonzero gain. At every offset strictly between $r_1$ and $r_2$ the gain is zero. Induction on this same pair therefore keeps all subsequent actions and histories equal through offset $r_2-1$, irrespective of any dependence on the first useful response. Stopping at any of these common histories would produce one answer for two different targets. No correct competitor can have a uniform bound below $r_2$.

The worlds in this argument are fixed for the given competitor before executing it on either selected source. Their selection uses the word already determined by a source-independent history, not a succession of response-dependent replacements of a source. They realize the entire common prefix and every subsequent action used in the contradiction. Together with the two attained upper bounds, this proves (16.1) without linearity, continuity, measurability, a countable answer palette, or any other regularity premise. It does not say that every individual interior response has a collision; the singleton response in Corollary 9.2 remains possible. $\square$

## 17. Sharp budgets on each fiber and delayed exterior savings

**Corollary 17.1 (each fixed interior fiber has the sharp full degree budget).** Fix $T\ge2$, $b\in I_T$, and any fixed known allowed $D$. For each integer $0\le s\le k$, the optimal uniform continuation budget over all known gains of actual degree $s$, with the entire $\mathcal F_b$ retained, is exactly $s+2$. Over all nonzero gains of degree at most $k$ it is exactly $k+2$. These statements hold for every fixed interior $b$, including $b\ne\phi$.

**Proof.** Among the first $s+2$ future integer clocks at least two are nonroots, so $r_2\le s+2$. Theorem 16.1 gives the upper bound. For the matching lower bound take the single common gain

$$
H_s(t)=c\prod_{j=2}^{s+1}(t-(T+j)),\qquad c\ne0.
\tag{17.1}
$$

The empty product for $s=0$ is $1$. This gain has actual degree $s$, with $r_1=1$ and $r_2=s+2$. Since $b\in I_T$, the second branch of Theorem 16.1 proves that its uniform optimum is $s+2$. Its fixed collision worlds use the same arbitrary allowed $D$. Taking $s=k$ proves the degree-at-most-$k$ lower bound, and root counting proves its upper bound. Coefficients of either sign are allowed. The construction places its zeros after the first useful read; zeros before that read can instead yield the saving below. For comparison, the already established exterior budgets of Theorem 11.1 are $s+1$ and $k+1$ for each fixed $b\notin I_T$. $\square$

**Corollary 17.2 (a finite exit criterion away from the golden crossing).** Define

$$
\ell_T(b)=\min\{j\ge1:b\notin I_{T+j-1}\},
\tag{17.2}
$$

with value $+\infty$ if this set is empty. For $b\in I_T\setminus\{\phi\}$ this is finite and at least $2$, while $\ell_T(\phi)=+\infty$. For every known $H,D$, formula (16.1) is equivalently $C_T=r_1$ when $r_1\ge\ell_T(b)$ and $C_T=r_2$ otherwise.

**Proof.** The intervals are nested by (11.2)–(11.3), contain $\phi$ strictly by Theorem 9.1, and have length

$$
U_S-L_S=\frac1{F_{S-1}F_S}\longrightarrow0.
\tag{17.3}
$$

Cassini gives the equality, and the Fibonacci recurrence gives unbounded denominators. Thus every fixed $b\ne\phi$ is outside all sufficiently late intervals. Nesting includes the equality endpoints in the exit side, and (16.1) proves the claimed reformulation. This criterion does not change the original degree budget or assume that a comparison of arbitrary real inputs is effectively decidable. $\square$

**Example 17.3 (an interior saving on the actual paid trajectory).** Take $k=1,d=0$, $N=5$, $T=4$, $b=8/5$, $H(t)=t-5$, and $D(t)=0$. This fiber is realized, for example, by

$$
P=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix};
$$

no promise that this is the actual representative is supplied. One has $b\in I_4=(3/2,5/3)$, while $r_1=2,r_2=3$ and $b=8/5$ is an endpoint of $I_5=(8/5,5/3)$. Perform $M$ at original clock $5$ and retain its zero-gain read; then perform $J$ at clock $6$. The terminal matrix $JM^5$ is injective on the entire $\mathcal F_{8/5}$, so (16.2) and Corollary 9.2 recover any actual source in it. The exact additional cost is $2$, rather than $r_2=3$, and the total after the five paid calibration reads is $7$. This saves one read against the interior actual-degree guarantee $N+s+2=8$, without skipping the root clock or excluding any source from the fiber.

## 18. A consumer after the paid polynomial calibration

**Theorem 18.1 (exact continuation count for the prescribed architecture).** In (13.1), start with the paid pure-$M$ prefix of

$$
N=2k+d+3\quad\hbox{reads},\qquad T=N-1=2k+d+2.
$$

Use its existing exact calibration to obtain $H,D,b$, and then apply Theorem 16.1. For these particular calibrated data the minimum uniform total read bound among protocols with this prescribed prefix is

$$
N+
\begin{cases}
r_1,&b\notin I_{N+r_1-2},\\
r_2,&b\in I_{N+r_1-2}.
\end{cases}
\tag{18.1}
$$

For each fixed $b$ at this $T$, the exact uniform totals over gains of actual degree $s\le k$ are

$$
\begin{cases}
N+s+1=2k+d+s+4,&b\notin I_T,\\
N+s+2=2k+d+s+5,&b\in I_T.
\end{cases}
\tag{18.2}
$$

Over degree at most $k$ these become $3k+d+4$ on the exterior and $3k+d+5$ on the interior. The last number is a uniform upper bound for this architecture on the full source domain; no unrestricted pre-calibration optimum is asserted.

**Proof.** Reuse the prefix part of Theorem 39.2 of [*FIB Self-Calibrating Relation Mathematics*](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#39-任意已知有限次共同增益的零安全固定历史恢复), as in Theorem 12.1. Its normalized $R_0$ is the present $P$; its gain and drift are exactly $H,D$ at the same original integer clocks. The $N$ reads at $0,\ldots,N-1$ recover the coefficient polynomials $H,bH,D$, and a nonzero coefficient of $H$ determines $b$. No sampled nonzero gain, sign restriction, exact maximum degree, or nonvanishing second spectral mode is needed. All $N$ reads, including the initial one, have been paid.

Proposition 8.2 shows that the compatible source set after this actual prefix is exactly the entire $\mathcal F_b$, with common histories for fixed $H,D,b$. Thus Theorem 16.1 applies without an extra source promise and gives (18.1), both its decoder and its adaptive lower bound. Adding the paid $N$ to Theorem 11.1 and Corollary 17.1 gives (18.2) and its sharpness for each fixed $b$. A prescribed-prefix protocol cannot stop on a partial pure-$M$ history and still recover all sources of this same fiber, since the common-history obstruction already holds there. Giving calibration freely in the continuation lower bound only makes a competitor stronger. Hence those lower bounds apply to this paid-prefix architecture as well. This conclusion leaves protocols that mix earlier or use a different calibration outside its sharpness scope. $\square$

## 19. Source correspondence and applicability

The integer input to Lemma 13.2 is the existing signed literal-word bound of main Lemma 25.1 and its `raw_word_fibonacci_bounds` declaration. The consequence (13.2) uses it twice and does not reprove or replace its induction. The determinant and mediant arithmetic in Lemma 13.3 is the classical Farey-neighbor fact cited there. The positive-direction pair and its strict-positivity checks come from (9.6)–(9.10); Lemma 14.1 supplies the additional nonpositive-direction argument and transposition needed for arbitrary terminal words. Theorem 15.1 combines these inputs at the actual literal length. Theorem 16.1 combines its universal obstruction with common original-world histories, and attains the resulting count using the already established exterior inverse and two-moving-trace basis. Theorem 39.2 supplies the paid calibration in Theorem 18.1. Neither calibration, the old next-$J$ exterior classification, the quadratic exterior inverse, nor the two-trace inverse is a new result here.

All scalar comparisons, polynomial evaluations, divisions at certified nonzero gains, and matrix inversions in these statements are over exact real numbers. No finite-precision, noise-robust, uniform conditioning, bit-complexity, or effective-real comparison conclusion follows. In particular a comparison of a general presented real $b$ with a rational endpoint, or a test that a general real polynomial value equals zero, needs an additional effective representation contract before it is an executable numerical test. These are optimal counts in the ideal exact-real read model.

The collision lower bounds retain one actual source, one whole gain polynomial, one whole drift polynomial, and the same original clock in each world. They concern uniform recovery on $\mathcal F_b$, not the assertion that all individual response fibers collide. Strict positivity is used both in the collision constructions and in the endpoint inverse; replacing it by nonnegativity would require another boundary analysis. Root multiplicity affects the polynomial degree but not the number of distinct failed integer-clock reads. All root clocks in the attained protocols have real paid $M$ or $J$ actions.

These ordinary mathematical proofs do not supply a new Lean verification or an external-priority claim. The global optimum over unrestricted original acquisition protocols, noisy or approximate recovery, and the wider research programme are not settled by the calibrated and prescribed-prefix optimality statements above.

## 追加锚（本行以下为增补区）

## 20. Post-calibration bounded error on the whole normalized fiber

**Definition 20.1 (source loss, effective error, and stable read budgets).** Retain Definition 13.1, including the particular exact $H,D,b$, the entire strictly positive source set $\mathcal F_b$, and the actual paid prefix $M^T$, $T\ge2$. At a subsequent nonroot clock $i$ the effective observation is

$$
 y_i=\operatorname{tr}(A_iP)+\eta_i,\qquad |\eta_i|\le\varepsilon.
 \tag{20.1}
$$

At a root clock the observation remains exactly $D(i)$. Only the post-calibration nonroot effective scalars are perturbed. The prefix and supplied calibration are exact. Errors are arbitrary bounded deterministic numbers; they need not be independent or have zero mean. Actions, stopping, and the estimate can be arbitrary deterministic functions of the whole received history, the exact calibration, and $\varepsilon$. Each action still incurs its mandatory read at the next original clock, including every gain root.

The estimate is any $\widehat P\in\operatorname{Mat}_2(\mathbb R)$, without positivity, rank, trace, or fiber constraints. Its complete-target answer is $(\widehat P,H,D)$ and its loss is $\|\widehat P-P\|_{\max}$. For an integer additional-read bound $q\ge0$, define

$$
 R_q(\varepsilon)=\inf_{\mathcal A}\ \sup_{P\in\mathcal F_b,\ |\eta_i|\le\varepsilon}
       \|\widehat P_{\mathcal A}-P\|_{\max},
 \tag{20.2}
$$

where each competing strategy stops within $q$ additional reads for every source and allowed error history. The infimum is separately taken for each $\varepsilon$; thus competitors may form arbitrary $\varepsilon$-dependent families. The asymptotic uniformly consistent budget is the least fixed $q$ for which $R_q(\varepsilon)\to0$ as $\varepsilon\downarrow0$. The asymptotic linear-error budget is the least fixed $q$ for which $R_q(\varepsilon)=O(\varepsilon)$. Equivalently these conditions permit a family of strategies attaining the stated rate: an extra error $\varepsilon^2$ in selecting an infimum suffices. Rate constants can depend on the exact $T,b,H,D$ and $q$, and never on the actual source or error. Neither definition permits an uncounted root wait.

For a fixed terminal matrix $A$ put

$$
 \Omega_{A,b}(\tau)=\sup\{\|P-Q\|_{\max}:P,Q\in\mathcal F_b,
                   |\operatorname{tr}(A(P-Q))|\le\tau\}.
 \tag{20.3}
$$

A uniformly continuous inverse means injectivity on the entire fiber and $\Omega_{A,b}(\tau)\to0$. A global Lipschitz inverse means $\|P-Q\|_{\max}\le L|\operatorname{tr}(A(P-Q))|$ for a finite $L$ and every pair in the fiber. These are comparisons of the same source pair under the same actual matrix.

If instead an original post-calibration observation has error $\xi_i$, exact subtraction and nonroot division give

$$
 \eta_i=\frac{\xi_i}{H(i)},\qquad
 |\xi_i|\le\delta_i\ \Longrightarrow\ |\eta_i|\le\frac{\delta_i}{|H(i)|}.
 \tag{20.4}
$$

Thus (20.1) corresponds exactly to the original weighted bounds $|\xi_i|\le\varepsilon|H(i)|$ at nonroots. For a fixed finite set of used nonroots, a common original bound $\delta$ gives effective bound $\delta\max_i|H(i)|^{-1}$. Root observations can be discarded using the known root pattern; replacing a perturbed root response by its known $D(i)$ adds no information. This last preprocessing allows upper bounds to handle original error also at root reads. It does not perturb the prefix or the calibration and gives no conditioning uniform over nonzero gains of arbitrary magnitude.

**Proposition 20.2 (the actual closure and the fixed-offdiagonal correspondence).** In the coordinates

$$
 P(t,v)=\begin{pmatrix}1-t&b-t-v\\v&t\end{pmatrix},\qquad
 F_b(t,v)=t^2-tv-v^2-t+bv,
 \tag{20.5}
$$

let $\mathcal K_b$ be the closure of $\mathcal F_b$ in the ambient matrix space. For $b\ne1$ it is exactly the nonnegative algebraic fiber $F_b(t,v)=0$, $0\le t\le1$, $v\ge0$, $b-t-v\ge0$. For $b=1$ that algebraic fiber has the extra isolated point $\left(\begin{smallmatrix}0&0\\0&1\end{smallmatrix}\right)$, and $\mathcal K_1$ is the algebraic fiber with this point removed. In particular every $\mathcal K_b$ is compact, without adding any source to $\mathcal F_b$.

The fixed-offdiagonal fibers of main §§23–32 are different fibers. Specifically, for their $x,\zeta>0$, normalizing $R_U(s)$ by $x$ and putting $t=s/x$, $a=\zeta/x$ gives

$$
 R_U(s)/x=\begin{pmatrix}1-t&t(1-t)/a\\a&t\end{pmatrix},\qquad
 \operatorname{tr}(MR_U(s)/x)=a+t+\frac{t(1-t)}a.
 \tag{20.6}
$$

For $R_V$ the off-diagonal entries are interchanged and the same last formula holds. The expression in (20.6) is nonconstant on $0<t<1$; fixing $b$ selects at most two of its parameters. Consequently their exact fixed-offdiagonal inverse moduli and action frontiers do not by normalization become whole-$\mathcal F_b$ results.

**Proof.** Trace, $M$ trace, and determinant give (20.5), with $u=b-t-v$ and $uv=t(1-t)$. All entries lie between $0$ and $\max(1,b)$ on the nonnegative algebraic fiber, which is closed and bounded. At $0<t<1$, its equation forces $u,v>0$, so these points already belong to $\mathcal F_b$. At $t=0$ its two endpoints are $(u,v)=(b,0),(0,b)$. Near the first, the equation solves as $v=t/b+O(t^2)$, with positive $u,v$ for small positive $t$; transposition handles the other. At $t=1$, a point exists only if $b\ge1$, and $uv=0$, $u+v=b-1$. For $b>1$, near $(u,v)=(b-1,0)$ one has $v=(1-t)/(b-1)+O((1-t)^2)$, again giving positive approximants; transpose for the other endpoint. These expansions follow by solving the displayed quadratic, or by its nonzero partial derivative in $v$ at the indicated endpoint.

For $b=1$, put $h=1-t$. Then $u+v=h$ and $uv=h(1-h)$. If $h>0$, $uv\le h^2/4$ forces $h\ge4/5$. Thus the point with $t=1$ is isolated and cannot be approached by positive sources; all remaining boundary points have the approximants already given. Removing an isolated point here leaves a closed bounded set. This proves exactly the claimed closure, including its exceptional point. Substitution of $s=xt$, $\zeta=ax$ in the main §23 formulas proves (20.6); its quadratic coefficient is $-1/a\ne0$. $\square$

## 21. The two different endpoint geometries

**Theorem 21.1 (whole-fiber canonical stability and its two sharp boundaries).** Fix $S\ge2$ and write

$$
 c=F_S,\qquad \rho=F_{S-1}/F_S,\qquad
 b_t=1/\rho,\qquad b_c=1+\rho,\qquad
 \lambda_S(P)=\operatorname{tr}(JM^SP).
 \tag{21.1}
$$

The two numbers $b_t,b_c$ are distinct and are the endpoints of $I_S$. On the entire $\mathcal F_b$ the following classification holds.

* For $b$ strictly outside the closed interval with endpoints $b_t,b_c$, $\lambda_S$ has a global Lipschitz inverse.
* At $b=b_t$, it has a global Hölder inverse of exponent $1/2$, and no finite global Hölder bound of any exponent greater than $1/2$. For the single noisy scalar and arbitrary ambient estimates, its minimax risk is $\Theta(\sqrt\varepsilon)$ as $\varepsilon\downarrow0$.
* At $b=b_c$, it is exactly injective, but

$$
 \Omega_{JM^S,b_c}(0)=0,\qquad
 \Omega_{JM^S,b_c}(\tau)=b_c\quad(\tau>0).
 \tag{21.2}
$$

For every $\varepsilon>0$, its single-scalar minimax risk over arbitrary ambient estimates is exactly $b_c/2$.

* In $I_S$ it is not injective, as in Theorem 9.1.

The geometric assertions also hold for $\ell_\theta(P)=v-\theta t$ with any positive rational $\theta$, with endpoints $1/\theta,1+\theta$. For this version (21.2) uses $\ell_\theta$ in (20.3). Nonzero scalar scaling and an additive known constant affect finite stability coefficients, but not the classification or the positive-error radius at the collapsed endpoint.

**Proof.** Use the already established canonical trace formula (9.4):

$$
 \lambda_S(P)=c+F_{S-1}b+c(v-\rho t).
 \tag{21.3}
$$

It suffices to analyze $\ell_\theta=v-\theta t$. Put $C=\theta^2+\theta-1\ne0$, since $\theta$ is positive rational. The positive-source collision calculation (9.5)–(9.10) applies with $\theta$ in place of $\rho$. It already proves exact injectivity outside the open endpoint interval and positive-source collisions inside it. We examine the actual closure from Proposition 20.2, rather than inferring stability from injectivity on an open set.

First classify possible equal-trace pairs on that closure. If $Q\ne P$ and $\ell_\theta(Q)=\ell_\theta(P)$, interchange the two so that

$$
 Q-P=h\begin{pmatrix}-1&-(1+\theta)\\\theta&1\end{pmatrix},\qquad h>0.
 \tag{21.4}
$$

Then $P_{11}\ge h>0$. If $Q_{11}>0$, the row-ratio derivation of (9.6) remains valid with $0\le x<y<\infty$. Its common $b$ is (9.7), a weighted average of $1/\theta$, $1+\theta$, and $(2+\theta)/(1+\theta)$ with weights $\theta$, $x+y$, and $(1+\theta)xy$. The first two weights are positive. The third value is strictly between the first two by (9.9), so $b$ is strictly between the endpoints. If $Q_{11}=0$, (21.4) gives $Q_{21}>0$; determinant zero then gives $Q_{12}=0$, $Q_{22}=1$. Writing $p=P_{11}=h\in(0,1]$ gives

$$
 P_{12}=p(1+\theta),\quad P_{21}=\frac{1-p}{1+\theta},\quad
 b=\frac{2+\theta}{1+\theta}
            +p\left(\theta-\frac1{1+\theta}\right).
 \tag{21.5}
$$

For $p<1$ this is strictly between the endpoints; for $p=1$ it equals $1+\theta$. Thus on either closed exterior sector the only possible distinct closure pair is, at $b=1+\theta$,

$$
 A=\begin{pmatrix}1&1+\theta\\0&0\end{pmatrix},\qquad
 Z=\begin{pmatrix}0&0\\\theta&1\end{pmatrix}.
 \tag{21.6}
$$

Both are actual closure points, since $b>1$. In particular the closure is still injective at $b=1/\theta$ and strictly outside the closed interval.

We also need tangent directions, since absence of distinct closure collisions alone does not prove a Lipschitz inverse. Away from $b=\phi$ the conic (20.5) is nonsingular: solving both zero partial derivatives and $F_b=0$ forces $b^2-b-1=0$. All exterior and endpoint values under consideration differ from $\phi$. A tangent annihilated by $\ell_\theta$ has direction (21.4). At a point with $P_{11}>0$, write its row ratio as $x\ge0$. The first derivative of the determinant in that direction vanishes exactly when

$$
 \frac{P_{12}}{P_{11}}=
       \frac{1+(1+\theta)x}{x+\theta}.
$$

Trace normalization therefore gives the tangent's fiber value

$$
 b(x)=\frac{(2+\theta)x^2+2(1+\theta)x+1}
                 {(1+\theta)x^2+2x+\theta}.
 \tag{21.7}
$$

For $x>0$ this is a strict weighted average of the same three values. At $x=0$ it equals $1/\theta$, at the source $A_t=\left(\begin{smallmatrix}1&1/\theta\\0&0\end{smallmatrix}\right)$. At a point with $P_{11}=0$, the endpoint with $P_{21}=0$ has nonzero determinant derivative $-1-\theta(b-1)$; the other endpoint has zero derivative only when $b=(2+\theta)/(1+\theta)$, strictly inside the interval. This also accounts for the limit $x\to\infty$ in (21.7). Hence strictly outside the closed interval there are neither closure collisions nor annihilated tangents; at $b=1/\theta$ the only annihilated tangent is at $A_t$.

For completeness, these geometric facts give global estimates as follows. On a regular local parametrization of the compact actual closure, a nonzero scalar derivative bounds matrix distance by a constant times scalar distance for two sufficiently nearby points in that chart. A finite collection of such charts covers the closure in the strictly exterior case. Pairs outside these local neighborhoods form a compact set disjoint from the diagonal; injectivity on the closure makes their scalar separation have a positive minimum. Its finite diameter then supplies the remaining Lipschitz bound. This uses the actual $\mathcal K_b$, including the removal at $b=1$.

At $b=1/\theta$, solve (20.5) for $v$ near $A_t$ using $t$ as parameter. Direct coefficient comparison gives

$$
 v(t)=\theta t+\theta C t^2+O(t^3),\qquad
 \ell_\theta(P(t))=\theta C t^2+O(t^3),\qquad t\ge0.
 \tag{21.8}
$$

These are actual positive sources for all sufficiently small $t>0$. Analyticity gives a neighborhood and constants $a,L>0$ in which

$$
 |\ell_\theta(P(t))-\ell_\theta(P(s))|
       \ge a|t^2-s^2|\ge a|t-s|^2,\qquad
 \|P(t)-P(s)\|_{\max}\le L|t-s|.
 \tag{21.9}
$$

Indeed the derivative of the second expression in (21.8) has the fixed sign of $C$ and absolute value at least a positive constant times $t$; integration proves (21.9). The other charts have the previous Lipschitz bound. Combining this chart with those charts and the compact separated-pair set yields a finite global Hölder $1/2$ bound. The two positive sources $P(t),P(2t)$ have distance at least $t$ and scalar separation $O(t^2)$. Their ratios for every exponent greater than $1/2$ diverge, proving sharpness on the original positive domain.

Here is also an attained noise bound with the declared ambient-estimator domain. Project the noisy scalar to the compact realized scalar set of $\mathcal K_b$ and apply its unique inverse, using the least scalar in case of a tie. The selected scalar differs from the true one by at most $2\varepsilon$. The exterior or tangent estimate just proved gives error at most $2L_b\varepsilon$ or $C_b\sqrt{2\varepsilon}$, respectively. Boundary outputs are allowed ambient estimates. For the canonical scalar, obtain that closure point using the existing quadratic (9.11) of Corollary 9.2, with membership in the actual $\mathcal K_b$ as the admissibility condition; the preceding geometry proves uniqueness. Conversely any two positive sources with scalar separation at most $2\varepsilon$ admit the same midpoint observation, and the triangle inequality forces error at least half their distance for one of them, regardless of the estimate's domain. Taking $P(t),P(2t)$ with $t$ a sufficiently small fixed multiple of $\sqrt\varepsilon$ gives the matching square-root lower bound.

Finally at $b=1+\theta$, (21.6) has equal $\ell_\theta$ values and distance $b$. To exhibit strictly positive worlds, use (8.3)–(8.5) at this fixed $b$: put

$$
 q(r)=\frac{b-r}{1-(b-1)r},\qquad
 P_r=P(r,q(r)),\qquad Q_r=P(r^{-1},q(r^{-1})).
 \tag{21.10}
$$

For every sufficiently small positive $r$, both arguments $q(r),q(r^{-1})$ are positive, so both matrices are actual sources in the same $\mathcal F_b$. They tend to $A,Z$, respectively. Their scalar difference tends to zero and their matrix distance tends to $b$. Every source has diagonal entries in $(0,1)$ and off-diagonal entries in $(0,b)$, so its whole-fiber diameter is at most $b$ and (21.10) attains this supremum at every positive scalar tolerance. Exact injectivity gives the zero-tolerance statement. The midpoint-observation lower bound therefore gives minimax risk at least $b/2$ for every positive error. The constant ambient estimate

$$
 \widehat P_0=\begin{pmatrix}1/2&b/2\\b/2&1/2\end{pmatrix}
 \tag{21.11}
$$

has error at most $b/2$ for all sources, proving equality. Known translation and nonzero scaling of the scalar preserve this argument for every positive error. Formula (21.3) completes all canonical assertions. $\square$

## 22. Stability thresholds at every literal terminal length

**Theorem 22.1 (all-word uniform and Lipschitz thresholds).** Fix $T\ge2$, $n\ge1$, put $S=T+n-1$, and retain all literal continuations $E_n\cdots E_1M^T$ with exactly $n$ actions and mandatory reads. There exists one whose terminal scalar has a uniformly continuous inverse on the entire $\mathcal F_b$ if and only if

$$
 b\notin I_S\quad\hbox{and}\quad b\ne1+F_{S-1}/F_S.
 \tag{22.1}
$$

There exists one with a global Lipschitz inverse if and only if $b$ is strictly outside the closed interval $\overline I_S$. Both attained conditions use the actual chronological continuation $M^{n-1}J$. At the other endpoint $b=F_S/F_{S-1}$ it gives the sharp square-root inverse of Theorem 21.1. These statements concern the terminal scalar; they do not discard earlier useful observations in a whole-history problem.

**Proof.** Sufficiency follows from Theorem 21.1 for the attained terminal matrix $JM^S$. The entire open interval is excluded by the all-word exact obstruction, Theorem 15.1. It remains to exclude uniform continuity at the collapsed endpoint and Lipschitz inversion at the tangent endpoint for every literal word, including noncanonical words.

Write $A=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&\delta\end{smallmatrix}\right)$ for an arbitrary such terminal matrix and set $e=\beta-\gamma$, $f=\delta-\alpha-\gamma$. Lemma 13.2 gives $|e|\le F_S$, at the literal length $S+1$. If $e=0$, transposed nonsymmetric sources give the exact collision of Lemma 14.1. If $e\ne0$, its scalar is the known constant $\alpha+\gamma b$ plus $e(v-\theta t)$ with $\theta=-f/e$. For $1<b<2$, Lemma 14.1 says that injectivity requires

$$
 \theta\in K_b\quad\hbox{or}\quad -1-\theta\in K_b.
 \tag{22.2}
$$

Each of these rational numbers has reduced denominator at most $F_S$. Transposition exchanges them, up to a sign and a known scalar constant, and is an isometry of $\mathcal F_b$ in the matrix norm.

Let $u=F_{S-2}/F_{S-1}$ and $v=F_{S-1}/F_S$. The Farey determinant and denominator calculation in Lemma 13.3 says that the only rationals in the closed interval with endpoints $u,v$ having denominator at most $F_S$ are its endpoints. No new word-bound induction is required. At $b_c=1+v$ and $S\ge3$, $K_{b_c}$ is the interval from $v$ to $1/(1+v)$; the second endpoint lies strictly inside the Farey interval from $u$ to $v$. Hence the only permitted value in (22.2) is $v$. Every injective terminal scalar is therefore a nonzero affine rescaling of $\ell_v$, possibly after transposition. Theorem 21.1 gives its positive-error discontinuity on the whole fiber. Noninjective scalars already fail uniform continuity.

At $b_t=1/v=1+u$ and $S\ge3$, $K_{b_t}$ is the entire interval from $u$ to $v$. Thus an injective terminal scalar must, after the same possible transposition, use $\ell_v$ or $\ell_u$. The first has the square-root boundary at $b=1/v$; the second has the collapsed boundary at $b=1+u$. Neither has a Lipschitz inverse. This argument also supplies, for each injective candidate of tangent type, strictly positive pairs whose source distance is of order $t$ while their trace separation is of order $t^2$.

There are two low-order endpoint issues. For $S=2$, necessarily $T=2,n=1$. The only terminal matrices are $M^3$, constant on $\mathcal F_b$, and $JM^2$. At $b_t=1$ use its actual closure $\mathcal K_1$, not the extra isolated algebraic point; Theorem 21.1 gives precisely the square-root inverse. At $b_c=2$ the same theorem gives the collapsed pair, so no other word repairs it. For $S=3$, the tangent endpoint is $b_t=2$, outside the strict range of Lemma 14.1. Its necessary condition (22.2) still holds at $b=2$: the positive-$\theta$ collision construction (14.5) for $\theta\notin[1/2,1]$ is unchanged; for $-1<\theta\le0$ its limiting row ratios are $x_0=-\theta<1$ and $y_0=1$, so the same small positive perturbation gives strictly positive collisions. The case $\theta=-1$ is the transpose of $\theta=0$, and $\theta<-1$ is again reduced by transposition. Thus the only permitted denominator-at-most-two slopes are $u=1$ and $v=1/2$, giving respectively the collapsed and tangent geometries just proved. The collapsed endpoint $b_c=3/2$ is already within the ordinary range. These cases exhaust $S\ge2$ and prove both necessary thresholds. $\square$

## 23. Asymptotic stable costs on one actual history

**Theorem 23.1 (first-two-nonroot stable budgets against adaptive families).** In Definition 20.1 let $r_1<r_2$ be the first two positive nonroot offsets of the particular known $H$, and put $S=T+r_1-1$. The asymptotic uniformly consistent and linear-error additional-read budgets are exactly

$$
 C_T^{\rm uc}(b;H,D)=
 \begin{cases}
 r_1,& b\notin I_S\ \hbox{and}\ b\ne1+F_{S-1}/F_S,\\
 r_2,&\hbox{otherwise},
 \end{cases}
 \tag{23.1}
$$

$$
 C_T^{\rm lin}(b;H,D)=
 \begin{cases}
 r_1,& b\notin\overline I_S,\\
 r_2,&\hbox{otherwise}.
 \end{cases}
 \tag{23.2}
$$

At $b=F_S/F_{S-1}$ and every fixed $r_1\le q<r_2$, one has $R_q(\varepsilon)=\Theta(\sqrt\varepsilon)$. All lower bounds allow arbitrary ambient estimates and deterministic strategies depending on $\varepsilon$. Every upper bound is achieved on one mandatory-read trajectory, retaining all gain-root actions and the original clocks.

**Proof of attainment.** On either $r_1$ branch, execute $M$ at each offset less than $r_1$ and $J$ at offset $r_1$. The terminal matrix is $JM^S$. Theorem 21.1's compact-image projection decoder, using the actual closure only, has uniform linear error strictly outside $\overline I_S$ and uniform square-root error at the tangent endpoint. It reads precisely $r_1$ times, even when all preceding gains vanish.

For every other case execute $J$ at offset $1$ and then $M$ at every offset through $r_2$. Retain the noisy effective traces at $r_1,r_2$. Reuse the exact two-moving-trace basis and inverse in Lemmas 3.1–3.2 and (16.3):

$$
 \mathcal L(P)=\bigl(\operatorname{tr}P,\operatorname{tr}(MP),
  \operatorname{tr}(M^{r_1-1}JM^TP),
  \operatorname{tr}(M^{r_2-1}JM^TP)\bigr).
 \tag{23.3}
$$

This is a fixed linear isomorphism on all real matrices. Return

$$
 \widehat P=\mathcal L^{-1}(1,b,y_{T+r_1},y_{T+r_2}).
 \tag{23.4}
$$

Writing $L_1=\mathcal L^{-1}(0,0,1,0)$ and $L_2=\mathcal L^{-1}(0,0,0,1)$, the ordinary finite-dimensional error estimate is explicitly

$$
 \|\widehat P-P\|_{\max}
 \le (\|L_1\|_{\max}+\|L_2\|_{\max})\varepsilon.
 \tag{23.5}
$$

In original error units it is bounded by

$$
 \|L_1\|_{\max}\frac{\delta_{T+r_1}}{|H(T+r_1)|}
 +\|L_2\|_{\max}\frac{\delta_{T+r_2}}{|H(T+r_2)|}.
 \tag{23.6}
$$

These constants are finite for the fixed known gain and actual indices. No positivity projection, division by a root, second trajectory, or unacquired trace is used. This is the inherited double-moving-trace inverse with noisy right sides, rather than a new calibration result.

**Proof of necessity.** Fix an error level and one competitor with uniform read bound $q<r_2$. Proposition 8.2 makes the whole paid prefix and supplied $H,D,b$ identical on every source in $\mathcal F_b$. Every offset before $r_1$ is a gain root and has exactly the same response $D(T+j)$, whatever actions have been selected. Induction fixes a common word up to the first nonroot, independent of $P$. If $q<r_1$, any two fixed distinct positive sources remain on the same history, giving a fixed positive minimax lower bound.

If the competitor stops before $r_1$ on that source-independent history, the same fixed-pair obstruction already applies, regardless of its larger allowed bound $q$. Otherwise it actually reaches $r_1$, and its matrix $A$ there is a literal continuation of length $r_1$, fixed before its response is seen. Choose two actual positive sources $P,Q$ for that fixed matrix with trace separation at most $2\varepsilon$, and give both worlds the common midpoint effective response. Each world's error has magnitude at most $\varepsilon$. The two complete worlds are $(P,H,D)$ and $(Q,H,D)$ with their same exact full polynomials. All later clocks through offset $q$ are roots, so induction preserves the common actual actions and observations, even if they depend on the midpoint response. Any stopping estimate on that history is the same ambient matrix in both worlds. Its worst loss is at least $\|P-Q\|_{\max}/2$. Stopping on the common history after $r_1$ gives the same obstruction; if needed its history can be padded through $q$ with ignored mandatory root reads. The worlds are fixed for this competitor and error level before either run; they are not replaced as the history evolves.

There are only finitely many possible words through offset $r_1$, even though the competitor can depend arbitrarily on $\varepsilon$. In the interior $b\in I_S$, Theorem 15.1 supplies a strictly positive exact collision for each word; the minimum of the finitely many positive collision distances is positive. At the collapsed endpoint, Theorem 22.1 shows that each word either has such a collision or has the collapsed geometry of Theorem 21.1, up to nonzero scaling and possible transposition. In the latter case strictly positive pairs have arbitrarily small scalar separation and distance tending to $b$. Again a positive lower bound can be chosen uniformly over the finite word set for all sufficiently small $\varepsilon$. Thus no such family with $q<r_2$ is uniformly consistent on these branches.

At the tangent endpoint, every word either has a positive collision, has the collapsed geometry, or has the quadratic tangent geometry identified in Theorem 22.1. In the third case the positive pairs from (21.8)–(21.9), rescaled for that particular trace, force risk at least $a_A\sqrt\varepsilon$ for small $\varepsilon$, where $a_A>0$. In the other cases a constant lower bound also implies a square-root lower bound for sufficiently small $\varepsilon$. Taking the minima of these finitely many positive constants and error cutoffs gives $R_q(\varepsilon)\ge a\sqrt\varepsilon$. The canonical $r_1$ construction gives its matching upper bound, and in particular excludes uniform $O(\varepsilon)$ error below $r_2$. Together with the root-wait lower bound and attained decoders, this proves (23.1)–(23.2), including arbitrary $\varepsilon$-dependent deterministic choices. $\square$

## 24. Paid calibration consumers and degree-controlled gaps

**Theorem 24.1 (stable totals after exact paid polynomial calibration).** Start with the actual pure-$M$ prefix of $N=2k+d+3$ reads at original clocks $0,\ldots,N-1$, so $T=N-1\ge2$. Retain the complete exact calibration returned by the prefix of main Theorem 39.2. For every fixed resulting $H,D,b$, the uniformly consistent and linear-error total budgets for this prescribed architecture are exactly

$$
 N+C_T^{\rm uc}(b;H,D),\qquad N+C_T^{\rm lin}(b;H,D),
 \tag{24.1}
$$

respectively. The complete source fiber remains $\mathcal F_b$. The exact total budget remains the already proved Theorem 18.1; (24.1) compares a different, positive-error task on that same source domain.

**Proof.** The prefix theorem recovers the coefficient polynomials $H,bH,D$ at these exact original clocks; a nonzero coefficient of $H$ returns $b$, including all gain roots and degree drops. Its fixed-known-node confluent interpolation is the established Hermite ingredient, as represented by Batenkov–Yomdin, *On the Accuracy of Solving Confluent Prony Systems*, §2B, Definitions 2.3–2.4 and (2.2)–(2.4), [arXiv:1106.1137v3](https://arxiv.org/abs/1106.1137v3). Only that known-node linear evaluation fact is used here, not their unknown-node nondegeneracy or stability hypotheses. The calibration and its read count are reused premises, not inferred from the new perturbation model.

Proposition 8.2 identifies the compatible positive sources with exactly $\mathcal F_b$, all having this same entire exact prefix. Add the $N$ already paid reads to Theorem 23.1's attained continuation and common-history lower bound. A protocol constrained to this prefix cannot resolve the fiber by stopping on a shorter pure-$M$ history. Freely supplying the calibration in the lower bound only strengthens the competitor. This proves (24.1) within the prescribed architecture. No statement about noisy calibration, unknown $H,D,b$, or the unrestricted optimum over earlier mixed trajectories follows. $\square$

**Proposition 24.2 (the original seven-read example needs eight reads for uniform stability).** Keep precisely Example 17.3: $k=1,d=0,N=5,T=4,b=8/5,H(t)=t-5,D=0$, with the whole $\mathcal F_{8/5}$. Its exact total optimum for the prescribed prefix is $7$, while both stable totals in (24.1) are $8$. One actual eight-read trajectory has the following explicit robust decoder. Execute $J$ at clock $5$ and $M$ at each of clocks $6,7$. The clock-$5$ action and its zero-gain read are paid. Write the two received effective nonroot scalars as $y_6,y_7$ and set

$$
 \widehat v=\frac{131}{5}-y_6-y_7,\qquad
 \widehat t=\frac{212}{5}-y_6-2y_7,\qquad
 \widehat u=-67+2y_6+3y_7,\qquad
 \widehat P=\begin{pmatrix}1-\widehat t&\widehat u\\\widehat v&\widehat t\end{pmatrix}.
 \tag{24.2}
$$

For every source and every finite effective error bound $\varepsilon\ge0$ it has $\|\widehat P-P\|_{\max}\le5\varepsilon$. If the original errors at clocks $6,7$ have magnitude at most $\delta$, its error is at most $7\delta/2$. For every $\varepsilon>0$, every deterministic family constrained to the same exact prefix and at most seven total reads has worst error at least $543/1090$.

**Proof.** Here $r_1=2,r_2=3,S=5$, $F_4/F_5=3/5$, and $b=1+3/5=b_c$. The exact seven-read assertion is the existing example and Theorem 18.1. Theorem 23.1 gives the all-source stable lower bound at $r_2=3$, allowing arbitrary intervening words and ambient outputs. An explicit positive lower constant is also available. The four possible terminal matrices after two more actions are $M^6,JM^5,MJM^4,M^4$. For $JM^5$, Theorem 21.1 gives risk $4/5$ at every positive error. For each other matrix the two strictly positive sources

$$
 P'=\frac1{545}\begin{pmatrix}470&750\\47&75\end{pmatrix},\qquad
 P''=\frac1{545}\begin{pmatrix}108&207\\228&437\end{pmatrix}
 \tag{24.3}
$$

are in $\mathcal F_{8/5}$ and have equal terminal traces. For $M^6,M^4$ this follows from the pure-$M$ identity (8.6); for $MJM^4$ direct multiplication gives zero trace pairing with their difference. Their distance is $543/545$. They have the same entire prefix and same whole $H,D$, and clock $5$ is a root. Thus their actual two-read histories coincide and the midpoint lower bound gives $543/1090$. The first action and the action at clock $6$ are fixed on the common history before that first nonroot response; early stopping cannot improve this lower bound. This proves the asserted constant for every permitted strategy.

For the attained eight-read path, direct multiplication gives

$$
 A_6=MJM^4=\begin{pmatrix}2&3\\5&8\end{pmatrix},\qquad
 A_7=M^2JM^4=\begin{pmatrix}5&8\\7&11\end{pmatrix}.
$$

For $P=\left(\begin{smallmatrix}1-t&u\\v&t\end{smallmatrix}\right)$, $u+v+t=8/5$, their exact traces are $10+t-2v$ and $81/5-t+v$. Solving these two linear equations is exactly (24.2) without error. If their effective errors are $a,e$, the errors of $v,t,u$ are $-a-e,-a-2e,2a+3e$. Their maximum absolute value is at most $5\varepsilon$ when $|a|,|e|\le\varepsilon$. Since $H(6)=1,H(7)=2$, original error at most $\delta$ instead gives $|a|\le\delta$, $|e|\le\delta/2$ and the bound $7\delta/2$. These estimates are uniform over the entire fiber and impose no output constraints. This trajectory uses the already paid five reads and precisely three further reads; it does not change the separate exact trajectory $M$ at clock $5$, $J$ at clock $6$ in Example 17.3. $\square$

**Proposition 24.3 (arbitrarily large exact/stable gaps with controlled degree).** Fix $k,d\ge0$, $0\le s\le k$, the paid prefix $N=2k+d+3$, $T=N-1$, any allowed exact $D$, and

$$
 H_s(t)=c_*\prod_{j=2}^{s+1}(t-(T+j)),\qquad c_*\ne0.
 \tag{24.4}
$$

The empty product is $1$. At $b=1+F_{T-1}/F_T$, the exact total optimum is $N+1$, whereas both stable totals are $N+s+2$. Their gap is exactly $s+1$. At $b=F_T/F_{T-1}$ the exact and uniformly consistent totals are $N+1$, with sharp square-root risk at that budget, whereas the linear-error total is $N+s+2$. Thus increasing the declared degree permits arbitrarily large gaps without changing the normalized strictly positive source domain or omitting any root read.

**Proof.** This is the existing root arrangement (17.1), now used at the endpoint fibers: $\deg H_s=s$, $r_1=1$, and $r_2=s+2$. Exact endpoint injectivity and the already proved exact budget (16.1) give the $N+1$ exact totals. Apply (23.1)–(23.2) at $S=T$ and add the paid prefix. For the collapsed fiber both stable notions wait for the second nonroot; for the tangent fiber the first nonroot already has the sharp square-root decoder, while linear error requires the second. The full lower bounds retain $H_s$ itself and the same entire $D$ in both worlds. These are fixed-gain, prescribed-prefix comparisons; they assert neither optimal finite-error coefficients nor an unrestricted global optimum for the original uncalibrated model. $\square$

## 追加锚（本行以下为增补区）

## 25. Raw bounded error with unknown calibration: two whole-world obstructions

**Definition 25.1 (all-read contract and original-clock loss).** In §§25–29 fix known integers $k,d\ge0$, and retain the strictly entrywise positive rank-one trace-one source $P$, the atoms $M,J$, left multiplication, and mandatory consecutive original-clock reads of Definition 8.1. A world has one fixed $P$, one whole $0\ne H\in\Pi_k$, and one whole $D\in\Pi_d$. Its received reports are

$$
 \widetilde z_i=H(i)\operatorname{tr}(A_iP)+D(i)+\xi_i,
 \qquad |\xi_i|\le\delta,
 \qquad \delta\ge0.
 \tag{25.1}
$$

The bound applies to every paid read, including the initial read, all calibration reads, and every gain root. Errors are arbitrary deterministic numbers. No $H,D,b=\operatorname{tr}(MP)$, root pattern, source bound, or sampled-gain lower bound is supplied. An ambient answer $(\widehat P,\widehat H,\widehat D)$ has complete-target loss

$$
 \mathcal L=\max\{\|\widehat P-P\|_{\max},
       \|\operatorname{coeff}_k(\widehat H-H)\|_\infty,
       \|\operatorname{coeff}_d(\widehat D-D)\|_\infty\}.
 \tag{25.2}
$$

Here $\operatorname{coeff}_r$ means the padded monomial vector at the original variable $t$, through degree $r$. It is not a coefficient vector after translating or rescaling the clock, nor a uniform norm over all real times. Each competitor can depend arbitrarily on $\delta$ and its entire received history, including its actions, stopping, and answer. A finite worst-case total cap counts the initial read and every subsequent atomic action/read. There are no empty actions, resets, copies, inverse acquisitions, skipped reads, unread composites, second trajectories, or side sensors.

For a source class and fixed cap, source minimax risk is the infimum over such deterministic protocols of the supremum of $\|\widehat P-P\|_{\max}$ over the declared whole worlds and all allowed errors. Complete-target risk uses (25.2). Uniform consistency means that risk tends to zero as $\delta\downarrow0$; a uniform linear-error guarantee means a bound $C\delta$ for all sufficiently small $\delta$, with one finite class-wide $C$. Different protocols may be used at different error levels. This contract differs from Definition 20.1: no calibration quantity or prefix read is exact when $\delta>0$.

**Theorem 25.2 (infinite unrestricted source risk at every positive raw error).** For every $\delta>0$ and every finite worst-case total cap, source minimax risk on the original unrestricted source class is infinite, even restricted to $D=0$ and constant gains $H\in[1,2]$. This includes arbitrary deterministic adaptive protocols and any finite cap chosen as a function of $\delta$.

**Proof.** Fix a positive integer cap $n$. Let $\mathcal W_n$ be all cumulative matrices of literal words of lengths $0,\ldots,n-1$, including $I$, and set

$$
 W_n=\max_{A\in\mathcal W_n}\sum_{a,b}|A_{ab}|,
 \qquad e=\min\{1/2,\,2\delta/W_n\}>0.
 \tag{25.3}
$$

These are finite sets of actual matrices, so $2\le W_n<\infty$. For $x\ge1$ take the two complete worlds with $D_1=D_2=0$, $H_1=1$, $H_2=1+e$, and

$$
 P_x=\begin{pmatrix}1/2&x\\1/(4x)&1/2\end{pmatrix},
 \qquad
 Q_x=\begin{pmatrix}1/2&x/(1+e)\\(1+e)/(4x)&1/2\end{pmatrix}.
 \tag{25.4}
$$

Both sources are strictly positive, have trace one and determinant zero, and therefore have rank one. Their effective-source difference is

$$
 H_1P_x-H_2Q_x=
 \begin{pmatrix}-e/2&0\\-(2e+e^2)/(4x)&-e/2\end{pmatrix}.
 \tag{25.5}
$$

Its maximum norm is at most $e$. For every $A\in\mathcal W_n$, the two noiseless reports consequently differ by at most $W_ne\le2\delta$. Give both worlds their midpoint report at every matrix reached by the protocol. Each world's error has magnitude at most $\delta$. Determinism inductively makes their actions, received histories, stopping, and answer identical. This induction uses the same two whole worlds throughout: (25.5) holds simultaneously at every possible matrix through the cap, before selecting the realized branch. Once that branch is determined, its errors are ordinary fixed finite sequences in the two runs.

The common estimate has loss at least half the source distance in one of these worlds, whereas

$$
 \|P_x-Q_x\|_{\max}\ge xe/(1+e)\longrightarrow\infty.
 \tag{25.6}
$$

Thus every capped protocol has infinite worst source loss. No-report protocols have the same conclusion directly. Taking the infimum proves the theorem. All gains stay in the fixed compact positive interval $[1,2]$; no vanishing-gain explanation is used here. $\square$

**Proposition 25.3 (bounded sources do not cure arbitrarily small gains).** Even on two fixed bounded strictly positive normalized sources, with $D=0$ and a common positive constant gain permitted to approach zero, no family of finite-cap deterministic protocols is uniformly consistent. The cap may grow arbitrarily as $\delta\downarrow0$, provided it is finite at each positive $\delta$.

**Proof.** Take

$$
 P^{(0)}=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},
 \qquad P^{(1)}=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix}.
 \tag{25.7}
$$

Their maximum distance is $3/10$. For a cap $n=n(\delta)$ put

$$
 V_n=\max\left\{1,\max_{A\in\mathcal W_n}
              |\operatorname{tr}(A(P^{(0)}-P^{(1)}))|\right\},
 \qquad h_\delta=\min\{\delta,\,2\delta/V_n\}>0.
 \tag{25.8}
$$

Use the same whole constant $H=h_\delta$ in both worlds. Their reports differ by at most $2\delta$ at every possible read through the cap. The midpoint-history argument in Theorem 25.2 gives worst loss at least $3/20$. Every world still has nonzero gain; choosing harder allowed worlds separately for different $\delta$ is precisely the uniform-risk quantifier. $\square$

## 26. One fixed acquisition and an all-error decoder without root decisions

**Definition 26.1 (fixed linear ingredients and degree-only constants).** Set

$$
 N=2k+d+3,\qquad T=N-1,\qquad L=N+k+2=3k+d+5,
 \tag{26.1}
$$

and acquire exactly the actual trajectory

$$
 A_i=M^i\quad(0\le i<N),\qquad
 A_{N+r}=G_r=M^rJM^T\quad(0\le r\le k+1).
 \tag{26.2}
$$

Thus $T$ individual $M$ actions are followed by one $J$ and $k+1$ individual $M$ actions. There are $L$ reads at clocks $0,\ldots,L-1$, with no restarting of $H,D$ or the clock. Let $f_i,g_i$ be the Fibonacci solutions with initial values $(f_0,f_1)=(1,0)$ and $(g_0,g_1)=(0,1)$. Write $\mathsf V$ for the square $N$-row matrix whose row $i$ is

$$
 \big((f_i i^j)_{j=0}^k,\ (g_i i^j)_{j=0}^k,
                                      \ (i^j)_{j=0}^d\big),
 \qquad 0\le i<N,
 \tag{26.3}
$$

with $i^0=1$, including at zero. Main Definition 39.1 and Theorem 39.2 in [*FIB Self-Calibrating Relation Mathematics*](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#39-任意已知有限次共同增益的零安全固定历史恢复) supply its invertibility and its exact coefficient output $(H,bH,D)$. This is a reused calibration map, not an assumed exact measurement. Define

$$
 (\widehat h,\widehat q,\widehat a)
       =\mathsf V^{-1}(\widetilde z_0,\ldots,
                                  \widetilde z_{N-1})^{\mathsf T},
 \quad \widehat H(t)=\sum_{j=0}^k\widehat h_jt^j,
 \quad \widehat D(t)=\sum_{j=0}^d\widehat a_jt^j,
 \quad a=\max\{1,\|\mathsf V^{-1}\|_{\infty\to\infty}\}.
 \tag{26.4}
$$

The symbol $a$ in §§26–28 is this fixed inverse bound. The following constants also depend only on $k,d$. Put $n_r=N+r$ and

$$
 E_j=\max_{0\le r\le k+1}\sum_{v=0}^j n_r^v,
 \qquad \Lambda=\max\left\{1,\max_{0\le r\le k+1}
                                      \sum_{u,v}|(G_r)_{uv}|\right\}.
 \tag{26.5}
$$

For every subset $S\subset\{n_0,\ldots,n_{k+1}\}$ of size $k+1$, let $V_S=(x^j)_{x\in S,\,0\le j\le k}$, with rows in increasing order, and set

$$
 c=\left(\max\{1,\max_S\|V_S^{-1}\|_{\infty\to\infty}\}\right)^{-1}>0.
 \tag{26.6}
$$

The inverses here are the classical Lagrange interpolation inverses, also recorded in Lemma 2.1 of [*Common Polynomial-Gain Shear Calibration and Erasure Recovery*](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md#2-elementary-polynomial-interfaces). Only that elementary polynomial fact is reused; its recorded-read acquisition model is not substituted for (26.2).

For $0\le p<q\le k+1$ let $\mathcal I_{p,q}$ be the inverse taking four traces against $I,M,G_p,G_q$ to a real matrix. Lemma 3.2 supplies every such inverse, including nonadjacent pairs. Its output norm is the maximum entry norm. Define

$$
 \Gamma=\max\{1,\max_{p<q}\|\mathcal I_{p,q}\|_{\infty\to\max}\},
 \quad s=\frac{c}{2\Gamma},\quad
 B=1+aE_d+aE_k\Lambda,
 \quad K=\sqrt{(k+1)a^2+(k+2)B^2},
$$

$$
 C_{k,d}=(K+2)\sqrt{s^{-2}+a^2}.
 \tag{26.7}
$$

All these constants are finite, specified by finite matrices, and independent of the actual source, gain, drift, and error level. No optimality of these constants is part of their definition.

**Theorem 26.2 (attained full-target recovery for every actual world and every error level).** On the trajectory (26.2) there is one decoder, using only its received raw records, $k,d$, and $\delta$, with

$$
 \|\operatorname{coeff}_k(\widehat H-H)\|_\infty\le a\delta,
 \qquad
 \|\operatorname{coeff}_d(\widehat D-D)\|_\infty\le a\delta,
$$

$$
 \|\widehat P-P\|_{\max}\le C_{k,d}\chi\delta,
 \qquad
 \chi=\frac{1+\operatorname{tr}(MP)}
                {\|\operatorname{coeff}_k H\|_\infty}.
 \tag{26.8}
$$

These inequalities hold simultaneously for every world in Definition 25.1, every $\delta\ge0$, and all allowed errors. The decoder needs neither $\chi$ nor a bound on it, neither exact calibration nor a root service. In particular it gives pointwise linear stability at every fixed original world and exact recovery when $\delta=0$.

**Proof and decoder.** First (26.4), the exact prefix supplier, and the elementary induced-norm inequality give

$$
 \|\widehat h-h\|_\infty\le a\delta,\quad
 \|\widehat q-bh\|_\infty\le a\delta,\quad
 \|\widehat a-\operatorname{coeff}_dD\|_\infty\le a\delta,
 \qquad h=\operatorname{coeff}_kH.
 \tag{26.9}
$$

This invokes the supplier only at the noiseless vector underlying the same actual prefix. It does not replace noisy records by acquired exact ones. In particular no noisy coefficient quotient is declared to be the true $b$.

For a coefficient vector $u\in\mathbb R^{k+1}$, write $u(t)=\sum_j u_jt^j$. In fixed entry coordinates $\operatorname{vec}(S)=(S_{11},S_{12},S_{21},S_{22})^{\mathsf T}$ define the $(3k+4)\times4$ matrix $\mathsf A_u$ by

$$
 \mathsf A_u\operatorname{vec}(S)=
 \left((u_j\operatorname{tr}S)_{j=0}^k,
       (u_j\operatorname{tr}(MS))_{j=0}^k,
       (u(n_r)\operatorname{tr}(G_rS))_{r=0}^{k+1}\right)^{\mathsf T}.
 \tag{26.10}
$$

Form solely from the acquired records

$$
 y=\left((\widehat h_j)_{j=0}^k,
          (\widehat q_j)_{j=0}^k,
          (\widetilde z_{n_r}-\widehat D(n_r))_{r=0}^{k+1}\right)^{\mathsf T},
 \qquad \mathsf A=\mathsf A_{\widehat h},
$$

$$
 \operatorname{vec}(\widehat P)=
       (\mathsf A^{\mathsf T}\mathsf A+\delta^2 I_4)^{-1}
                      \mathsf A^{\mathsf T}y.
 \tag{26.11}
$$

For $\delta>0$ this is a positive-definite inverse for every real received vector, even when $\widehat H$ vanishes identically. At $\delta=0$, actual records have $\widehat H=H\ne0$; the rank argument below proves the inverse exists. Formula (26.11) is a single formula at all actual error levels. The answer is allowed to be ambient. Neither a sampled gain nor a selected gain coefficient is a divisor in this decoder.

Here is the quantitative rank bound, using only the credited interpolation and four-trace inverses. Among the $k+2$ numbers $|u(n_r)|$, the second largest is at least $c\|u\|_\infty$: delete a largest one and apply the Lagrange inverse bound (26.6) to the remaining $k+1$ values. This includes $k=0$. For $u\ne0$, choose two such positions $p,q$ only for this estimate, and a coefficient with modulus $\|u\|_\infty$. For every real matrix $S$, its four traces in $\mathcal I_{p,q}$ are then bounded by $\|\mathsf A_u\operatorname{vec}(S)\|_\infty/(c\|u\|_\infty)$. Since $c\le1$ and $\|\operatorname{vec}(S)\|_2\le2\|S\|_{\max}$, it follows that

$$
 \|\mathsf A_u\operatorname{vec}(S)\|_2
          \ge s\|u\|_\infty\|\operatorname{vec}(S)\|_2.
 \tag{26.12}
$$

For $u=0$ the same inequality is trivial. Thus $\sigma=\sigma_{\min}(\mathsf A)\ge s\|\widehat h\|_\infty$, and $\sigma>0$ at every actual noiseless record. No selection of these two positions occurs in the decoder and no actual zero is tested.

Strict positivity and trace normalization give

$$
 b=P_{12}+P_{21}+P_{22}>0,\quad
 \|P\|_{\max}\le1+b,\quad
 \|\operatorname{vec}(P)\|_2\le2(1+b),\quad
 |\operatorname{tr}(G_rP)|\le\Lambda(1+b).
 \tag{26.13}
$$

Set $r=y-\mathsf A\operatorname{vec}(P)$. Its first $k+1$ coordinates vanish exactly, since $\operatorname{tr}P=1$. Its next coordinates equal $\widehat q_j-b\widehat h_j$, of modulus at most $a\delta(1+b)$. Its last coordinates equal

$$
 \xi_{n_r}+(D-\widehat D)(n_r)
          +(H-\widehat H)(n_r)\operatorname{tr}(G_rP),
 \tag{26.14}
$$

whose moduli are at most $B\delta(1+b)$. Consequently

$$
 \|r\|_2\le K\delta(1+b).
 \tag{26.15}
$$

This is where the same actual source, whole polynomials, and original clock are needed: the gain-estimation error multiplies the trace of this very source, including at a true root. It is not an independent lifted source or a separately calibrated future signal.

Use the elementary regularized-inverse singular-value estimates, with $\rho=(\sigma^2+\delta^2)^{1/2}$:

$$
 \|(\mathsf A^{\mathsf T}\mathsf A+\delta^2 I)^{-1}
                         \mathsf A^{\mathsf T}\|_{2\to2}\le\rho^{-1},
 \quad
 \|\delta^2(\mathsf A^{\mathsf T}\mathsf A+\delta^2 I)^{-1}\|_{2\to2}
                         \le\delta^2/\rho^2\le\delta/\rho.
 \tag{26.16}
$$

These are the usual scalar inequalities for the singular values $v$: $v/(v^2+\delta^2)\le1/\sqrt{v^2+\delta^2}$ and the corresponding inverse-square bound. They are standard linear-algebra estimates, not additional calibration results. For every actual record $\rho>0$, including $\delta=0$. Subtracting $\operatorname{vec}(P)$ in (26.11) and using (26.13)–(26.16) gives

$$
 \|\widehat P-P\|_{\max}
       \le(K+2)\frac{(1+b)\delta}{\rho}.
 \tag{26.17}
$$

Finally (26.9) and (26.12) imply

$$
 \|h\|_\infty\le\|\widehat h\|_\infty+a\delta
        \le\sigma/s+a\delta
        \le\sqrt{s^{-2}+a^2}\,\rho.
 \tag{26.18}
$$

Combining the last two inequalities proves the source bound in (26.8); (26.9) gives both entire-polynomial bounds. The proof covers arbitrary gain signs, degree drops, repeated roots, every sampled root, unbounded $b$, and arbitrary whole drift coefficients. Regularization, rather than a true-root decision or a supplied conditioning constant, makes the formula valid also when noise erases every estimated gain coefficient. $\square$

## 27. Acquired conditioning certificates and their conditional meaning

**Theorem 27.1 (one finite certificate for all compatible whole worlds).** Use the acquired quantities in (26.4). Set

$$
 m=\|\widehat h\|_\infty,\qquad \epsilon=a\delta,
 \qquad \alpha=m-\epsilon.
 \tag{27.1}
$$

When $\alpha>0$, the following computable numbers are a simultaneous certificate for every complete world compatible with these same $L$ records, the actual trajectory (26.2), and the declared bounds (25.1):

$$
 b\le b_{\rm cert}:=\frac{\|\widehat q\|_\infty+\epsilon}{\alpha},
 \qquad
 \chi\le\chi_{\rm cert}:=
       \frac1\alpha+\frac{\|\widehat q\|_\infty+\epsilon}{\alpha^2},
$$

$$
 \|\widehat P-P\|_{\max}\le C_{k,d}\chi_{\rm cert}\delta,
 \qquad
 \mathcal L\le\max\{a,C_{k,d}\chi_{\rm cert}\}\delta.
 \tag{27.2}
$$

When $\alpha\le0$, this certificate reports failure and makes no finite uniform source-recovery claim for that record. For every fixed original world, it succeeds for all sufficiently small $\delta$, uniformly over its allowed errors; as $\delta\downarrow0$, its $\chi_{\rm cert}$ tends to that world's $\chi$. Its validity is conditional on the declared model and noise bound; it does not certify those assumptions from the data.

**Proof.** For every compatible world, the same prefix inverse gives (26.9). Hence $\|h\|_\infty\ge\alpha>0$ and

$$
 b\|h\|_\infty=\|bh\|_\infty
       \le\|\widehat q\|_\infty+\epsilon.
 \tag{27.3}
$$

Since $b>0$, these inequalities prove the first two bounds in (27.2). Apply Theorem 26.2 separately to each such whole world; its decoder is the same function of the received data in all of them. This proves the simultaneous target certificate, without replacing compatible worlds by independent choices of prefix and tail.

If $h$ is the fixed original nonzero coefficient vector, then $m\ge\|h\|_\infty-\epsilon$, so

$$
 \alpha\ge\|h\|_\infty-2a\delta>0
 \quad\hbox{whenever}\quad
       \delta<\|h\|_\infty/(2a).
 \tag{27.4}
$$

Also $m\to\|h\|_\infty$ and $\|\widehat q\|_\infty\to b\|h\|_\infty$, uniformly over these errors. Substitution proves the claimed certificate limit.

The quantities are finite arithmetic expressions and norms of the actual coefficient output, with a sufficient strict positive margin. A positive margin can also be witnessed by certified enclosing intervals; no equality or zero test of an unknown true $H(i)$ is needed. At a nonpositive margin the rule supplies no recovery radius, not a proof that a particular compatible world is unrecoverable. The decoder (26.11) still exists at every actual record and retains its instancewise bound. No finite-bit input representation, arithmetic complexity, or total decision procedure for equality of arbitrary presented reals is asserted. $\square$

## 28. A sharp prescribed-prefix budget on explicit joint world classes

**Definition 28.1 (joint conditioning classes and prescribed-prefix risks).** For $R>0$ let

$$
 \mathcal C_R=\{(P,H,D)\hbox{ in Definition 25.1}:
       (1+\operatorname{tr}(MP))/\|\operatorname{coeff}_kH\|_\infty\le R\}.
 \tag{28.1}
$$

This is an explicit sufficient joint source/gain condition. Neither trace normalization nor $H\ne0$ implies membership. It imposes no separate upper bound on $P,H,D$, and the decoder is not supplied the true $\chi$ or $R$. Prescribed-prefix risks restrict competitors to the first $N$ pure-$M$ reads at clocks $0,\ldots,N-1$ as in (26.2), allowing any subsequent legal deterministic adaptive actions, stopping, and ambient answers. Uniform risks take the supremum over $\mathcal C_R$ and all raw errors. A fixed total cap, rather than a source-dependent or error-dependent unbounded wait, is the budget being minimized; the competitors themselves remain arbitrarily $\delta$-dependent.

**Theorem 28.2 (sharp consistency and linear-error caps for each $R>0$).** For every $k,d\ge0$ and every $R>0$, the least prescribed-prefix total cap for uniformly consistent complete-target recovery on $\mathcal C_R$ and the least such cap for uniform linear-error recovery are both

$$
 N+k+2=3k+d+5.
 \tag{28.2}
$$

The attained decoder is (26.11), with all-$\delta$ complete-target error at most $\max\{a,C_{k,d}R\}\delta$. Every smaller fixed cap has complete-target risk bounded below by a positive number independent of $\delta$, even with zero noise. Lower-bound competitors may be arbitrary deterministic $\delta$-dependent adaptive protocols without continuity, measurability, linearity, or answer-palette restrictions.

**Proof.** Theorem 26.2 gives the upper bound immediately on the stated joint class, at the same actual clocks and with every root read paid.

For the lower bound reuse the positive golden crossing fiber of Theorems 5.1–5.2. Every $P$ in that fiber has $b=\phi$ and $\operatorname{tr}(M^iP)=\phi^i$ at all pure-$M$ clocks. Choose one common whole polynomial and drift

$$
 F(t)=\prod_{r=0}^{k-1}(t-(N+r)),\qquad
 H_*(t)=\frac{1+\phi}{R\|\operatorname{coeff}_kF\|_\infty}F(t),
 \qquad D_*=0.
 \tag{28.3}
$$

The product is $1$ for $k=0$. Its coefficient norm is nonzero, $\deg H_*=k$, and every crossing-fiber world $(P,H_*,0)$ has exactly $\chi=R$. Thus the entire positive crossing fiber, rather than only selected source representatives, remains in $\mathcal C_R$.

Its full prescribed prefix is source-independent. Its first $k$ continuation clocks $N,\ldots,N+k-1$ are roots, whose exact reports are zero regardless of the actions. Determinism fixes the entire action/history branch through those clocks. If the competitor stops there, any fixed two distinct sources in the fiber give a positive error obstruction. If it reaches clock $N+k$, the last possible read under a total cap $N+k+1$, its matrix $A$ is fixed before this first nonroot response. Theorem 5.2 supplies two distinct strictly positive sources in the same crossing fiber with equal trace against this $A$. They have the same $H_*,D_*$, agree on the full prefix and every root read, and give the same last report. Their whole received histories and final answer coincide, so one source error is at least half their distance. Both are whole fixed worlds realizing this actual branch.

To make the obstruction uniform over error-dependent competitors, preselect one such collision pair for each of the finitely many matrices reached by literal continuation words of length $k+1$, and one fixed pair for early stopping. The minimum of their finitely many positive distances is positive. All shorter-cap competitors are included by permitting a larger cap $N+k+1$; early stopping is already covered. The same positive lower bound therefore holds separately at every $\delta$, using admissible zero errors throughout. It excludes both uniform consistency and a uniform $O(\delta)$ complete-target guarantee. This is precisely the inherited crossing-fiber/common-history obstruction applied inside the explicitly scaled joint class; it does not assume the competitor knows any calibration. $\square$

## 29. A five-read constant-gain consumer and supplier boundaries

**Proposition 29.1 (explicit all-raw five-read inverse and certificate).** For $k=d=0$, (26.2) is the legal trajectory with actions $(M,M,J,M)$ and cumulative matrices

$$
 I,\quad M,\quad M^2,\quad
 JM^2=\begin{pmatrix}1&2\\1&1\end{pmatrix},\quad
 MJM^2=\begin{pmatrix}1&1\\2&3\end{pmatrix}
 \tag{29.1}
$$

at original clocks $0,1,2,3,4$. Write its five received records as $y_0,\ldots,y_4$, its unknown nonzero constant gain as $h$, and its unknown constant drift as $D$. The following explicit ambient decoder is another attainment of the same budget:

$$
 x=y_2-y_1,\qquad q=y_2-y_0,\qquad
 \widehat h=x,\qquad \widehat D=y_0+y_1-y_2,
$$

$$
 \widehat S=
 \begin{pmatrix}
 y_0-y_1-2y_2+y_3+y_4&y_0-4y_2+y_3+2y_4\\
 -y_0+2y_2-y_4&-y_0+3y_2-y_3-y_4
 \end{pmatrix},
 \qquad
 \widehat P=\frac{x}{x^2+\delta^2}\widehat S.
 \tag{29.2}
$$

For every actual world and every $\delta\ge0$ the denominator is positive, and

$$
 |\widehat h-h|\le2\delta,\qquad
 |\widehat D-D|\le3\delta,\qquad
 \|\widehat P-P\|_{\max}\le11\sqrt5\,
                        \frac{1+b}{|h|}\delta.
 \tag{29.3}
$$

A usable simultaneous certificate replaces $\chi$ on the right by

$$
 \chi_{\rm cert}^{(0)}=
       \frac1\alpha+\frac{|q|+2\delta}{\alpha^2},
 \qquad \alpha=|x|-2\delta>0.
 \tag{29.4}
$$

Its complete-target radius is $\max\{3,11\sqrt5\chi_{\rm cert}^{(0)}\}\delta$. When $\alpha\le0$ it makes no finite source-radius claim. It eventually succeeds for every fixed $h\ne0$ as $\delta$ decreases. The five-read cap is sharp for both stable tasks on each $\mathcal C_R$ with the prescribed three-read pure-$M$ prefix.

**Proof.** For $P=\left(\begin{smallmatrix}1-t&u\\v&t\end{smallmatrix}\right)$, direct traces of (29.1) are

$$
 1,\quad b=t+u+v,\quad 1+b,\quad 1+u+2v,\quad 1+2u+v+2t.
 \tag{29.5}
$$

Substitution in the linear expressions in (29.2) gives, for exact records, $x=h$, $q=bh$, $\widehat D=D$, and $\widehat S=hP$. This is elementary fixed linear inversion of the five acquired traces; it is not a new general interpolation theorem. Row sums of absolute coefficients give, with raw error at most $\delta$ at every one of these clocks,

$$
 |x-h|\le2\delta,\qquad |q-bh|\le2\delta,\qquad
 |\widehat D-D|\le3\delta,\qquad
 \|\widehat S-hP\|_{\max}\le8\delta.
 \tag{29.6}
$$

In particular $x^2+\delta^2>0$ at every actual record: for $\delta>0$ it is immediate, while for $\delta=0$ one has $x=h\ne0$. Put $r_0=\sqrt{x^2+\delta^2}$. Subtracting $P$ in (29.2) yields

$$
 \|\widehat P-P\|_{\max}
 \le\frac{|x|}{x^2+\delta^2}
            \bigl(8\delta+2\delta\|P\|_{\max}\bigr)
       +\frac{\delta^2}{x^2+\delta^2}\|P\|_{\max}
 \le\frac{11(1+b)\delta}{r_0}.
 \tag{29.7}
$$

Here $\|P\|_{\max}\le1+b$. Also $|h|\le|x|+2\delta\le\sqrt5r_0$, proving (29.3). If $\alpha>0$, (29.6) gives $|h|\ge\alpha$ and $b|h|\le|q|+2\delta$, which prove the simultaneous certificate (29.4) exactly as in Theorem 27.1. Its margin is positive for every allowed record when $\delta<|h|/4$. Theorem 28.2 with $N=3$ proves sharpness in the declared architecture.

For a concrete whole world take

$$
 P=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},\qquad h=2,\qquad D=1.
 \tag{29.8}
$$

Its noiseless reports at these same original clocks are $(3,21/5,31/5,27/5,43/5)$. Formula (29.2) returns $x=2$, $q=16/5$, $\widehat D=1$, and $\widehat S=2P$ before normalization. With noisy records it retains (29.3), and every allowed record has a successful margin when $\delta<1/2$. No read, clock translation, or calibration observation is omitted. $\square$

**Assumptions and source correspondence for §§25–29.** Main Definition 39.1 and Theorem 39.2 supply the fixed pure-$M$ coefficient inverse and its exact paid-tail consumer, with normalized $R_0=P$, the same $H,D$, original integer clocks, arbitrary degree drops and gain roots, and $N=2k+d+3$. Their known-node ingredient is the confluent evaluation matrix and determinant in Batenkov–Yomdin, *On the Accuracy of Solving Confluent Prony Systems*, [§2B, arXiv:1106.1137v3](https://arxiv.org/html/1106.1137v3#S2.SS2). The nodes here are the fixed distinct nonzero $\phi,\psi$, both different from the drift node $1$. No unknown-node Prony stability theorem or nonzero highest modal amplitude is imported. Elementary Lagrange interpolation and induced-norm/singular-value estimates are credited tools; Lemma 3.2 supplies the moving-trace basis, and Theorems 5.1–5.2 supply the entire positive crossing fiber. The all-raw normalization, common-world residual, unrestricted obstructions, acquired certificate, and their joint-class acquisition consequences are the source-specific synthesis here (repo-derived); no external-priority claim is made.

The [trace-corridor theorem in *FIB Self-Calibrating Relation Mathematics IX*, §4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md#4-固定或有界读数的整个迹走廊) assumes its exact compatible ancestor equations, bounded ancestor vector, and a declared positive finite $J$-trace corridor. It is not an all-raw noisy normalization theorem on the unrestricted domain. The [six-read affine stability results, §§11–15](FIB_AFFINE_SIX_READ_SHARP_RECOVERY.md#11-norms-and-the-exact-six-read-stability-problem) concern their positive-intercept effective target and their recorded-reading clock, including an empty repeat and unread composites, with specified conditioning domains. Their exact-image pair estimates do not supply (26.11) for arbitrary raw perturbations. The polynomial shear volume likewise allows empty reads and unread composites. Its elementary interpolation fact is used in (26.6), but no cheaper acquisition history or clock convention is imported from either volume.

The exact results in §§2–19 and the exact-prefix/post-calibration-noise results in §§20–24 keep their own hypotheses and conclusions. Theorem 25.2 concerns the full original class; Theorem 26.2 gives an instancewise bound on that class; Theorem 27.1 gives a finite acquired certificate conditional on the original model; Theorem 28.2 gives uniform guarantees only on each expressly declared $\mathcal C_R$. No necessity or maximality of that class, source-local noisy-prefix optimum, unrestricted earlier-mixing optimum, optimal finite-noise constants, finite-bit arithmetic, physical realization, literature priority, or Lean certification is asserted.

## 追加锚（本行以下为增补区）

## 30. Finite record limits of sources escaping to infinity

**Definition 30.1 (compatible whole worlds and two limit spaces).** Fix any declared integers $k,d\ge0$ and exactly the $L=3k+d+5$ cumulative matrices and original clocks of (26.2). Retain the entire contract of Definition 25.1. For a legal whole world $W=(P,H,D)$ write its noiseless acquired vector as

$$
 Z(W)_i=H(i)\operatorname{tr}(A_iP)+D(i),\qquad 0\le i<L.
$$

For a received vector $y\in\mathbb R^L$ and a radius $\rho\ge0$, define

$$
 \mathcal W_\rho(y)=\{W\text{ legal}:\|Z(W)-y\|_\infty\le\rho\}.
 \tag{30.1}
$$

Each member uses its one fixed source and two whole polynomials at all $L$ paid reads; the corresponding deterministic errors are exactly $y_i-Z(W)_i$. Bounded complete targets means boundedness of $P$ in the maximum entry norm and of both padded original-variable coefficient vectors in (25.2). Put

$$
 U_i=(A_i)_{21},\qquad V_i=(A_i)_{12},
$$

$$
 \begin{aligned}
 \mathcal E_{12}&=\{(U_iQ(i)+F(i))_{i=0}^{L-1}:
                                  Q\in\Pi_k,\ F\in\Pi_d\},\\
 \mathcal E_{21}&=\{(V_iQ(i)+F(i))_{i=0}^{L-1}:
                                  Q\in\Pi_k,\ F\in\Pi_d\},\\
 e(y)&=\min\{\operatorname{dist}_\infty(y,\mathcal E_{12}),
             \operatorname{dist}_\infty(y,\mathcal E_{21})\}.
 \end{aligned}
 \tag{30.2}
$$

The subscripts name the escaping source entry: $\operatorname{tr}(A_iE_{12})=U_i$ and $\operatorname{tr}(A_iE_{21})=V_i$. In these auxiliary spaces $Q=0$ is allowed. This does not enlarge the actual-world contract, which still requires $H\ne0$.

Both spaces are linear subspaces of the finite-dimensional record space and hence closed. Their distances are attained: a minimizing sequence of record vectors is bounded, has a convergent subsequence, and its limit is in the closed subspace. Each distance is the standard Chebyshev linear program

$$
 \min_{Q\in\Pi_k,\,F\in\Pi_d,\,r\ge0}r,
 \qquad -r\le y_i-U_iQ(i)-F(i)\le r\quad(0\le i<L),
 \tag{30.3}
$$

with $V$ replacing $U$ for the second space. Only coefficients and the scalar $r$ are optimization variables; no new read, source, or calibration is introduced. This is the ordinary real-arithmetic LP representation, not a finite-bit algorithm for arbitrary presented reals.

**Theorem 30.2 (all finite record limits at unbounded source norm).** For every $k,d\ge0$, the set of vectors $z$ for which there exist legal whole worlds $W_n$ on (26.2) with

$$
 \|P_n\|_{\max}\longrightarrow\infty,
 \qquad Z(W_n)\longrightarrow z
 \tag{30.4}
$$

is exactly $\mathcal E_{12}\cup\mathcal E_{21}$.

**Proof.** Write every actual source as

$$
 P=\begin{pmatrix}1-t&u\\v&t\end{pmatrix},\qquad
 0<t<1,\quad u,v>0,\quad uv=t(1-t)\le1/4,
 \qquad b=t+u+v.
 \tag{30.5}
$$

For a sequence in (30.4), $b_n\to\infty$. Applying the fixed prefix inverse (26.4) to the bounded noiseless vectors gives bounded coefficient vectors of $H_n$, $b_nH_n$, and $D_n$. Consequently $\operatorname{coeff}_kH_n\to0$. Pass to a subsequence on which the coefficients of $b_nH_n$ and $D_n$ converge to polynomials $Q\in\Pi_k$ and $F\in\Pi_d$, and on which either $u_n\ge v_n$ always or $v_n\ge u_n$ always. Such a subsequence exists by finite-dimensional boundedness and the two alternatives.

In the first alternative $u_n\to\infty$, $v_n\le1/(4u_n)\to0$, and $u_n/b_n\to1$. For every acquired clock,

$$
 \frac{\operatorname{tr}(A_iP_n)}{b_n}
 =U_i\frac{u_n}{b_n}+V_i\frac{v_n}{b_n}
   +\frac{(A_i)_{11}(1-t_n)+(A_i)_{22}t_n}{b_n}
 \longrightarrow U_i.
 \tag{30.6}
$$

It follows that $z_i=U_iQ(i)+F(i)$. The other alternative gives $z_i=V_iQ(i)+F(i)$. Passing to a subsequence preserves the already specified limit $z$, so this proves necessity even for sequences alternating between the two source directions. In particular $Q$ can vanish: boundedness of $b_nH_n$ does not give a positive lower bound on it.

Conversely, fix any $Q\in\Pi_k$ and $F\in\Pi_d$. For $x\ge1$ use

$$
 P_x=\begin{pmatrix}1/2&x\\1/(4x)&1/2\end{pmatrix},\qquad
 D_x=F,\qquad
 H_x=\begin{cases}Q/x,&Q\ne0,\\x^{-2},&Q=0.\end{cases}
 \tag{30.7}
$$

Every source is strictly positive, rank one and trace one; every actual gain is a nonzero polynomial of the declared degree bound, including the $Q=0$ case. At each of the finitely many original clocks, direct substitution gives $Z(W_x)_i\to U_iQ(i)+F(i)$. Transposing $P_x$ gives every vector of $\mathcal E_{21}$ in the same way. Each parameter specifies one complete world across all paid reads, with no source or polynomial changed along its history. This proves sufficiency. $\square$

## 31. A quantitative separation certificate on the acquired record

**Definition 31.1 (a fixed residual constant).** At each original clock put $S_k(i)=\sum_{j=0}^k i^j$, with $0^0=1$, and define the degree-only constant

$$
 R_{k,d}=\max_{0\le i<L}S_k(i)
 \left(\max\{|(A_i)_{11}|,|(A_i)_{22}|\}
             +\frac12\max\{|(A_i)_{12}|,|(A_i)_{21}|\}\right).
 \tag{31.1}
$$

This finite constant is at least one, because $A_0=I$. It is calculated from the already specified trajectory, not supplied source or gain information. The symbols $a,C_{k,d}$ below remain exactly the constants of §26.

**Theorem 31.2 (strict separation bounds every compatible complete world).** Compute $(\widehat h,\widehat q,\widehat a)$ from the received prefix by (26.4). If

$$
 \gamma=e(y)-\rho>0,\qquad
 \ell=\gamma/R_{k,d},\qquad B_\rho=\|\widehat q\|_\infty+a\rho,
 \tag{31.2}
$$

then every $W\in\mathcal W_\rho(y)$ satisfies simultaneously

$$
 \begin{gathered}
 \ell\le\|\operatorname{coeff}_kH\|_\infty
                     \le\|\widehat h\|_\infty+a\rho,\qquad
 \|\operatorname{coeff}_dD\|_\infty\le\|\widehat a\|_\infty+a\rho,\\
 b\le b_{\rm sep}:=B_\rho/\ell,\qquad
 \|P\|_{\max}\le1+b_{\rm sep},\qquad
 \chi\le\chi_{\rm sep}:=\ell^{-1}+B_\rho\ell^{-2}.
 \end{gathered}
 \tag{31.3}
$$

Whenever $\mathcal W_\rho(y)\ne\varnothing$, the unchanged decoder (26.4), (26.10)–(26.11), used with radius $\rho$, is defined and has the simultaneous acquired-record bounds

$$
 \|\widehat P-P\|_{\max}\le C_{k,d}\chi_{\rm sep}\rho,
 \qquad
 \mathcal L\le\max\{a,C_{k,d}\chi_{\rm sep}\}\rho.
 \tag{31.4}
$$

In particular the compatible complete targets are bounded. Any established lower bound on $e(y)$ exceeding $\rho$ can replace $e(y)$ in (31.2): this only decreases $\ell$ and enlarges the resulting upper bounds. All bounds are conditional on the original model and the declared raw radius. A failed strict inequality supplies no impossibility conclusion for an exact record.

**Proof.** First consider any single legal world, without imposing a source bound. If $u\ge v$ in (30.5), then $v\le1/2$. The vector $w_i=U_i(uH)(i)+D(i)$ is in $\mathcal E_{12}$, and

$$
 \begin{aligned}
 |Z(W)_i-w_i|
 &=|H(i)|\left|(A_i)_{11}(1-t)+(A_i)_{22}t+V_iv\right|\\
 &\le R_{k,d}\|\operatorname{coeff}_kH\|_\infty.
 \end{aligned}
 \tag{31.5}
$$

Here $|H(i)|\le S_k(i)\|\operatorname{coeff}_kH\|_\infty$ and the diagonal term is a convex combination of the two diagonal entries. If $v\ge u$, use $u\le1/2$ and $w_i=V_i(vH)(i)+D(i)$ in $\mathcal E_{21}$. Thus every actual world satisfies

$$
 \operatorname{dist}_\infty(Z(W),\mathcal E_{12}\cup\mathcal E_{21})
          \le R_{k,d}\|\operatorname{coeff}_kH\|_\infty.
 \tag{31.6}
$$

For a world compatible with $y$ at radius $\rho$, the triangle inequality now gives $e(y)\le\rho+R_{k,d}\|\operatorname{coeff}_kH\|_\infty$, proving the inferred lower bound $\ell$. The same fixed prefix inverse gives (26.9) with $\delta=\rho$, hence

$$
 b\|\operatorname{coeff}_kH\|_\infty\le B_\rho.
$$

This proves the bound on $b$, both coefficient upper bounds, and

$$
 \frac{1+b}{\|\operatorname{coeff}_kH\|_\infty}
 \le\ell^{-1}+B_\rho\ell^{-2}.
$$

Use (26.13) for the source norm and Theorem 26.2 for the entire target. Its single decoder is the same function of $y,k,d,\rho$ in every compatible world. No independent prefix and tail realizations are combined. The coefficient lower bound is inferred; it asserts no lower bound on any particular sampled $H(i)$ and allows all actual gain roots. $\square$

**Proposition 31.3 (the coefficient certificates imply separation).** With $m=\|\widehat h\|_\infty$ from (27.1),

$$
 e(y)\ge m/a.
 \tag{31.7}
$$

Thus the positive margin $m-a\rho>0$ of Theorem 27.1 implies $e(y)>\rho$. For $k=d=0$ the positive margin of (29.4) also implies separation, since $e(y)\ge|y_2-y_1|/2$.

**Proof.** On every pure-$M$ prefix clock, $U_i=V_i=g_i$. The prefix of every vector in either limit space is therefore $g_iQ(i)+F(i)$. The inverse $\mathsf V^{-1}$ returns $(0,\operatorname{coeff}_kQ,\operatorname{coeff}_dF)$ on it. Applying the $H$-coefficient block of this inverse to $y-w$ gives $m\le a\|y-w\|_\infty$. Take the infimum over the two spaces. For $k=d=0$, every limit vector has equal coordinates at clocks $1,2$, so $|y_2-y_1|\le2\|y-w\|_\infty$ directly. Neither implication has a converse, as §33 shows. $\square$

## 32. Strict slack and the exact boundary for radius inflation

**Theorem 32.1 (robust boundedness and genuine source escape).** Fix $y$ and $\delta\ge0$ on the acquired trajectory (26.2).

1. If $e(y)>\delta$, every $0\le\eta<e(y)-\delta$ has bounded compatible complete targets in $\mathcal W_{\delta+\eta}(y)$, with the explicit bounds of Theorem 31.2 at $\rho=\delta+\eta$.
2. If $e(y)<\delta$, the source projection of $\mathcal W_\delta(y)$ is unbounded. This is actual whole-world compatibility at every paid clock, not a failed sufficient certificate.
3. There exists some $\eta>0$ for which $\mathcal W_{\delta+\eta}(y)$ has bounded complete targets if and only if $e(y)>\delta$. If $e(y)\le\delta$, its source projection is unbounded for every $\eta>0$.

At $e(y)=\delta$, these assertions leave exact-radius boundedness undecided. Sections 34–35 give actual consumers with opposite exact-radius outcomes.

**Proof.** The first assertion follows immediately from Theorem 31.2. For the second, choose a nearest vector $w$ in the union of the two limit spaces, so $\|y-w\|_\infty=e(y)$. Theorem 30.2 supplies legal whole worlds with $\|P_n\|_{\max}\to\infty$ and $Z(W_n)\to w$. Eventually

$$
 \|y-Z(W_n)\|_\infty
 \le e(y)+\|w-Z(W_n)\|_\infty<\delta.
 \tag{32.1}
$$

Every one of these worlds has the fixed deterministic raw errors $y_i-Z(W_n)_i$ within the declared radius at all reads. This proves genuine unboundedness. If instead $e(y)\le\delta$, the identical argument with $\delta+\eta$ in place of $\delta$ works for every $\eta>0$. Conversely a strict gap allows, for example, $\eta=(e(y)-\delta)/2>0$. This proves the equivalence.

For any fixed finite $y,\rho$, the prefix inverse bounds both coefficient vectors of every member of $\mathcal W_\rho(y)$, independently of the source. Hence boundedness of its source projection is equivalent to boundedness of its complete targets. This equivalence of bounded sets does not imply a positive gain floor or a uniform linear-error recovery constant. An unbounded source projection, on the other hand, gives unbounded worst source error for any fixed finite ambient answer to that record. The proof makes no claim that mere equality permits the strict inequality in (32.1) at radius $\delta$. $\square$

## 33. A legal record certified beyond both coefficient margins

**Proposition 33.1 (five acquired reads with an inferred gain floor).** Let $k=d=0$, use exactly the five paid clocks and actions (29.1), and receive

$$
 y=(1,7/4,11/4,13/4,7/2),\qquad \delta=1/2.
 \tag{33.1}
$$

This is a legal record: the fixed complete world

$$
 P=\begin{pmatrix}1/2&1/4\\1&1/2\end{pmatrix},\qquad H=1,\qquad D=0
 \tag{33.2}
$$

has exactly these noiseless reports and zero errors at every paid read. Both earlier coefficient margins are inconclusive. Nevertheless

$$
 e(y)=3/4,\qquad e(y)-\delta=1/4,
 \tag{33.3}
$$

and every compatible complete world has the explicit bounds

$$
 3/10\le h\le2,\qquad |D|\le3/2,\qquad
 b\le55/6,\qquad\|P\|_{\max}\le61/6,\qquad\chi\le305/9.
 \tag{33.4}
$$

Thus the unchanged section-26 decoder has $\mathcal L\le\tfrac12\max\{3,(305/9)C_{0,0}\}$. The section-29 decoder also has $\mathcal L\le\tfrac12\max\{3,(3355/9)\sqrt5\}$. These are finite simultaneous bounds, not claims of small error or optimal constants.

**Proof.** The source in (33.2) has positive entries, trace one and determinant zero. Formula (29.5) verifies all five reports. In this degree-zero case the prefix inverse is

$$
 \mathsf V^{-1}=\begin{pmatrix}0&-1&1\\-1&0&1\\1&1&-1\end{pmatrix},
 \qquad a=3,
$$

and the acquired values are $\widehat h=1$, $\widehat q=7/4$, $\widehat a=0$. The §27 margin is $1-3/2=-1/2$, while the §29 margin is $1-2(1/2)=0$.

The two limit spaces here are

$$
 \mathcal E_{12}=\operatorname{span}\{\mathbf1,(0,1,1,1,2)\},\qquad
 \mathcal E_{21}=\operatorname{span}\{\mathbf1,(0,1,1,2,1)\}.
 \tag{33.5}
$$

For the first space the contrast $y_3-y_1=3/2$ forces distance at least $3/4$. It is attained by $F=1,Q=3/2$, whose residual vector $y-(F+UQ)$ is $(0,-3/4,1/4,3/4,-1/2)$. For the second space the contrast $y_4-y_1=7/4$ forces distance at least $7/8$. It is attained by $F=7/4,Q=7/8$, whose residual is $(-3/4,-7/8,1/8,-1/4,7/8)$. This proves (33.3) by exact primal vectors and equal-coordinate lower bounds, without needing an optimizer implementation.

To sharpen the finite bounds, take any actually compatible world and denote its noiseless reports by $z$. The contrasts in (29.5), with the same source and gain throughout, give

$$
 h(1+v-t)=z_3-z_1\ge1/2,\qquad
 h(1+u+t)=z_4-z_1\ge3/4.
 \tag{33.6}
$$

The first factor $1+v-t$ is positive, hence $h>0$. If $u\ge v$, then $v\le1/2$ and $1+v-t\le3/2$, giving $h\ge1/3$. If $v\ge u$, then $u\le1/2$ and $1+u+t\le5/2$, giving $h\ge3/10$. Thus $h\ge3/10$ in all cases. Formula (29.6) gives

$$
 bh\le|y_2-y_0|+2\delta=11/4,
 \qquad h\le|y_2-y_1|+2\delta=2,\qquad |D|\le3\delta=3/2.
$$

Consequently $b\le55/6$ and $\chi=(1+b)/h\le305/9$. Equations (26.8) and (29.3) give the displayed complete-target bounds. No supplied gain floor, source bound or additional acquisition is used. $\square$

## 34. Bounded exact-radius contact with escape under every inflation

**Proposition 34.1 (a bounded complete-target contact consumer).** On the same five-read trajectory with $k=d=0$, take

$$
 y^{\rm B}=(0,2,0,0,0),\qquad \delta_{\rm B}=1.
 \tag{34.1}
$$

Then $e(y^{\rm B})=1$, the exact-radius compatible set is nonempty, and every one of its whole worlds satisfies

$$
 b\le1,\qquad\|P\|_{\max}\le1,\qquad
 -4\le h<0,\qquad |D-2|\le3.
 \tag{34.2}
$$

Its complete targets are therefore bounded at exactly the declared radius, although both coefficient margins fail. For every $\eta>0$, $\mathcal W_{1+\eta}(y^{\rm B})$ has unbounded source projection.

**Proof.** A legal complete witness is

$$
 P_* =\begin{pmatrix}9/10&3/10\\3/10&1/10\end{pmatrix},\qquad
 h=-1,\qquad D=9/5.
 \tag{34.3}
$$

It is strictly positive, trace one and rank one, and its five noiseless reports are $(4/5,11/10,1/10,-1/10,-3/10)$. The raw errors producing (34.1) are $(-4/5,9/10,-1/10,1/10,3/10)$, each of magnitude at most one. Every vector in either space (33.5) has equal coordinates $1,2$, whereas $y^{\rm B}_1-y^{\rm B}_2=2$. Thus both distances are at least one, and the constant vector $\mathbf1$ attains one in both spaces.

Now consider any compatible whole world and its five exact reports $z$. Compatibility gives $z_1\ge1$, $z_2\le1$, and $z_0\le1$. The exact identities $h=z_2-z_1$ and $h\ne0$ imply $h<0$. Moreover

$$
 h(b-1)=z_1-z_0\ge0,
$$

so $b\le1$. Formula (30.5) then bounds every source entry by one. Also $z_1\le3$, $z_2\ge-1$ give $h\ge-4$, and $D=z_0-h\in[-1,5]$ gives (34.2). For this record $|y_2-y_1|-2\delta=0$ and $m-a\delta=2-3=-1$. Boundedness at contact did not require a successful coefficient certificate.

For an explicit inflation family take $P_x$ from (30.7), let

$$
 b_x=x+1/2+1/(4x),\qquad H_x=b_x^{-2},\qquad D_x=1,
 \qquad x\ge1.
 \tag{34.4}
$$

All sources and gains are legal, and every parameter specifies a whole world at the same five original clocks. The five traces $r_i=\operatorname{tr}(A_iP_x)$ are positive and at most $2(1+b_x)$, directly from (29.5). Since $b_x\ge x\ge1$, their reports obey $z_i=1+r_i/b_x^2\to1$ simultaneously. More explicitly the clock-$1$ residual has magnitude

$$
 |y^{\rm B}_1-z_1|=|1-1/b_x|\le1,
$$

and at each of the other four paid clocks

$$
 |y^{\rm B}_i-z_i|=1+r_i/b_x^2
       \le1+2(1+b_x)/b_x^2\le1+4/x.
 \tag{34.5}
$$

Thus every $x\ge\max\{1,4/\eta\}$ belongs to $\mathcal W_{1+\eta}(y^{\rm B})$, with the displayed deterministic errors at every read, while $\|P_x\|_{\max}=x\to\infty$. Exact-radius boundedness is therefore strictly weaker than boundedness under some positive radius inflation. This statement is about a fixed record and its declared radii, not about pointwise small-noise recovery. $\square$

## 35. Unbounded exact-radius contact from actual whole worlds

**Proposition 35.1 (a contact consumer with a genuine unbounded family).** On the same five paid original-clock reads, receive

$$
 y^{\rm U}=(1,7/10,17/10,19/10,21/10).
 \tag{35.1}
$$

The source $P_*$ in (34.3), with the whole $H=1,D=0$, gives exactly this record with zero actual errors. Its distances to the two spaces are $3/5$ and $7/10$, respectively, so $e(y^{\rm U})=3/5$.

At radius $11/20$ both old coefficient margins are negative, but the new strict margin is $1/20$. Every compatible world has the explicit bounds

$$
 \|\operatorname{coeff}_0H\|_\infty\ge1/80,\qquad
 b\le144,\qquad \|P\|_{\max}\le145,\qquad\chi\le11600,
 \tag{35.2}
$$

and (26.11) has complete-target error at most $\tfrac{11}{20}\max\{3,11600C_{0,0}\}$. Boundedness persists for every radius inflation $0\le\eta<1/20$.

At the contact radius $\delta_{\rm U}=3/5$, in contrast, the exact-radius compatible source projection is unbounded.

**Proof.** Formula (29.5) applied to $P_*$, $h=1,D=0$ gives all five entries of (35.1). Equal coordinates $1,3$ in $\mathcal E_{12}$ force distance at least $|y^{\rm U}_3-y^{\rm U}_1|/2=3/5$. The approximant with $F=2/5,Q=9/10$ has residual $(3/5,-3/5,2/5,3/5,-1/10)$, proving equality. Equal coordinates $1,4$ in $\mathcal E_{21}$ force distance at least $7/10$; the constant approximant $F=7/5,Q=0$ has residual $(-2/5,-7/10,3/10,1/2,7/10)$, again proving equality. This displayed minimizing approximant uses the allowed zero auxiliary polynomial; every actual world still has nonzero gain.

For the radius $11/20$, $\widehat h=1$ and $a=3$, so the §27 margin is $1-33/20=-13/20$ and the §29 margin is $1-22/20=-1/10$. In (31.1) the five terms are $(1,3/2,5/2,2,4)$, so $R_{0,0}=4$ and $\ell=(1/20)/4=1/80$. Using the sharper prefix inequality $b|h|\le|y_2-y_0|+2\delta=9/5$ from (29.6) in the proof of Theorem 31.2 gives $b\le144$ and $\chi\le80+(9/5)80^2=11600$. The entire-polynomial errors still satisfy (26.9); (26.8) gives the stated bound through the unchanged decoder. The inflation assertion is Theorem 32.1.

To prove actual unboundedness at radius $3/5$, for every real $x\ge3$ take one whole world

$$
 P_x=\begin{pmatrix}1/2&x\\1/(4x)&1/2\end{pmatrix},\qquad
 H_x=\frac9{10x},\qquad D_x=\frac25-\frac9{10x}.
 \tag{35.3}
$$

All entries of $P_x$ are positive, its trace is one and determinant zero, and $H_x$ is a nonzero constant. Substituting this same triple into all five traces of (29.5) gives the exact residual vector $Z(W_x)-y^{\rm U}$

$$
 \left(-\frac35,
 \ \frac35-\frac9{20x}+\frac9{40x^2},
 \ -\frac25+\frac9{20x}+\frac9{40x^2},
 \ -\frac35+\frac9{20x^2},
 \ \frac1{10}+\frac9{10x}+\frac9{40x^2}\right).
 \tag{35.4}
$$

For every $x\ge3$, the second entry is between $0$ and $3/5$, because $-9/(20x)+9/(40x^2)\le0$ and $9/(20x)\le3/20$. The third lies between $-2/5$ and $-9/40$, the fourth between $-3/5$ and $-11/20$, and the fifth between $1/10$ and $17/40$. The first has magnitude exactly $3/5$. These ordinary inequalities prove that every paid read satisfies the raw error bound, uniformly for all $x\ge3$, by taking errors to be the negatives of (35.4). Yet $\|P_x\|_{\max}=x\to\infty$. This is a genuine contact obstruction on a fixed received record, not an inference from an inconclusive margin. Together with Proposition 34.1 it proves that equality alone cannot settle exact-radius boundedness; it does not classify all contacts. $\square$

## 36. Mathematical suppliers and scope of the acquired-record extension

The prefix inverse is supplied by main Definition 39.1 and Theorem 39.2 in [*FIB Self-Calibrating Relation Mathematics*, §39](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#39-任意已知有限次共同增益的零安全固定历史恢复), instantiated with the same normalized source $R_0=P$, whole $H,D$, declared degrees, and consecutive original clocks as (26.2). Its fixed-known-node confluent interpolation ingredient is Batenkov–Yomdin, [*On the Accuracy of Solving Confluent Prony Systems*, §2B, the confluent Vandermonde definitions and determinant](https://arxiv.org/html/1106.1137v3#S2.SS2). Only that known-node linear fact is used, including arbitrary degree drops and vanishing modal coefficients; no unknown-node Prony stability hypothesis is imported. Lemma 3.2 supplies the moving-trace inverses; the fixed-node interpolation and regularized decoder remain precisely §§26–27. Their proofs and acquisition costs are suppliers, not new calibration services.

The finite-dimensional norm-approximation and Chebyshev LP representation in (30.3) are standard tools: Stephen Boyd and Lieven Vandenberghe, [*Convex Optimization*, §6.1.1, “Basic norm approximation problem” and “Chebyshev or minimax approximation,” printed pp. 291–293](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=305). Closedness of linear subspaces, finite-dimensional subsequence compactness, and the triangle inequality are the other ordinary tools. The source-specific content is the exhaustion of finite acquired-record limits by the two explicit spaces, the residual bridge (31.5)–(31.6), its quantitative common-world certificate and exact inflation boundary, and the three legal consumers. These are repository-derived deductions, not an external-priority claim or an exhaustive literature classification.

The [exact-history source-escape theorem in *FIB Self-Calibrating Relation Mathematics IX*, §7](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md#7-任意末两读的精确源逃逸集合) conditions on its exact ancestor equations and a different six-read history. Its exact escape locus and its endpoint analysis do not classify noisy radius boxes around the full record (26.2). Its [§4 trace corridor](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md#4-固定或有界读数的整个迹走廊) also retains its declared positive finite corridor. The [affine six-read stability results, §§11–15](FIB_AFFINE_SIX_READ_SHARP_RECOVERY.md#11-norms-and-the-exact-six-read-stability-problem) retain their effective target, recorded-reading clock and conditioning domains. None of these different contracts is substituted for the original-clock all-raw model here.

Strict separation is necessary and sufficient for bounded complete targets after some positive inflation of this record's error radius. At the exact radius it is sufficient, strict overlap is an obstruction, and contact requires further information: no general contact classification is given. Recordwise finite boundedness, robustness to radius inflation, pointwise recovery as noise tends to zero, and uniform recovery over world classes remain distinct assertions. Theorem 25.2 and all prior exact and noisy results keep their hypotheses and conclusions. The certificate neither tests the physical model nor supplies feasibility of an arbitrary received vector. No new reads, reset, source copy, skipped read, gain-root oracle, a priori source/gain floor, unrestricted acquisition optimum, optimal numerical constants, finite-bit arithmetic guarantee, physical realization, literature priority or kernel certification follows from these ordinary real-arithmetic results.

## 追加锚（本行以下为增补区）

## 37. Two source parameters with the whole gain and drift still linear

Throughout §§37–43, fix arbitrary $k,d\ge0$, the exact $L=3k+d+5$ original clocks and matrices of (26.2), a received $y\in\mathbb R^L$, and $\delta\ge0$. Compatibility means exactly $\mathcal W_\delta(y)$ in Definition 30.1. In particular every actual world has one strictly positive rank-one trace-one $P$, one whole $0\ne H\in\Pi_k$, and one whole $D\in\Pi_d$; every paid read has its raw error bounded by $\delta$. The construction below decides source boundedness at that very radius, including $e(y)=\delta$.

**Definition 37.1 (two charts and their quadratic trace numerators).** For $\alpha,\beta>0$ put $s=\alpha+\beta$ and

$$
 X_{12}(\alpha,\beta)=
 \begin{pmatrix}\alpha&1\\\alpha\beta&\beta\end{pmatrix},
 \qquad
 X_{21}(\alpha,\beta)=
 \begin{pmatrix}\alpha&\alpha\beta\\1&\beta\end{pmatrix},
 \qquad P_\nu=X_\nu/s,\quad \nu\in\{12,21\}.
 \tag{37.1}
$$

Both matrices $P_\nu$ are strictly positive, rank one, and trace one. In the first chart $(P_{12})_{12}=1/s$, and in the second $(P_{21})_{21}=1/s$. With $U_i,V_i$ as in (30.2), define

$$
 \begin{aligned}
 B_{12,i}&=U_i+(A_i)_{11}\alpha+(A_i)_{22}\beta+V_i\alpha\beta,\\
 B_{21,i}&=V_i+(A_i)_{11}\alpha+(A_i)_{22}\beta+U_i\alpha\beta.
 \end{aligned}
 \tag{37.2}
$$

For whole polynomials $Q(\tau)=\sum_{j=0}^kq_j\tau^j$ and $F(\tau)=\sum_{j=0}^df_j\tau^j$, set $H=sQ$, $D=F$. Then at every original clock, simultaneously,

$$
 H(i)\operatorname{tr}(A_iP_\nu)+D(i)
       =B_{\nu,i}(\alpha,\beta)Q(i)+F(i).
 \tag{37.3}
$$

Here $\tau$ denotes the original polynomial variable; $s$ is a parameter indexing different whole worlds, not a rescaled acquisition clock. The identity is exact, including all clocks where $Q(i)=0$. Actual legality is $q\ne0$; no sign or sampled-value restriction is imposed on $Q$.

**Lemma 37.2 (exhaustion and bounded coefficient fibers).** Each chart parametrizes every allowed source. For fixed $\alpha,\beta>0$, the linear map

$$
 (q,f)\longmapsto
       \big(B_{\nu,i}Q(i)+F(i)\big)_{i=0}^{L-1}
 \tag{37.4}
$$

is injective. Consequently its inverse image of the closed radius-$\delta$ box around $y$ is either empty or a compact polytope in $\mathbb R^{k+d+2}$. This includes lower-dimensional polytopes and $\delta=0$.

**Proof.** For any allowed source $P$, use $\alpha=P_{11}/P_{12}$ and $\beta=P_{22}/P_{12}$ in the first chart. Trace one gives $\alpha+\beta=1/P_{12}$; determinant zero gives the remaining entry in (37.1). Division by $P_{21}$ gives the second chart in the same way. Conversely (37.1) verifies all source conditions directly, since $\det X_\nu=0$ and its trace is $s>0$.

To prove injectivity, suppose (37.4) vanishes. Interpret it by (37.3) with the fixed source $P_\nu$. On the first $N=2k+d+3$ clocks, the fixed inverse from main §39, already instantiated in (26.3)–(26.4), returns the coefficient vectors of $sQ$, $b sQ$, and $F$, where $b=\operatorname{tr}(MP_\nu)$. Its input is zero, so $sQ=0$ and $F=0$. Since $s>0$, both coefficient vectors vanish. An injective linear map between finite-dimensional normed spaces has a bounded inverse on its image. The inverse image of a bounded box is therefore bounded; it is closed and described by finitely many linear inequalities. This proves the compact-polytope assertion without any uniform-in-$s$ inverse estimate. $\square$

No endpoint of the original source fiber is removed by these coordinates. In the notation of (30.5), in chart $12$,

$$
 u=1/s,\qquad t=\beta/s,\qquad
 v=\alpha\beta/s=s\,t(1-t).
 \tag{37.5}
$$

Thus $t\to0$ or $t\to1$ at arbitrary rates is retained by $\alpha,\beta>0$ and $s\downarrow0$. At the limiting corner $B_{12,i}(0,0)=U_i$ and $B_{21,i}(0,0)=V_i$, but none of the actual-world tests below is performed at that corner.

## 38. Exact coefficient elimination by signed bases

**Definition 38.1 (finite determinant data).** Put $m=k+d+2$. Order the $2L$ labels $r=(i,\eta)$ by increasing $i$, with $\eta=+1$ followed by $\eta=-1$. For each chart define the row and the scalar

$$
 C_{\nu,i}=
   \big((B_{\nu,i}i^j)_{j=0}^k,\ (i^j)_{j=0}^d\big),\qquad
 R_{\nu,(i,\eta)}=\eta C_{\nu,i},\qquad
 \lambda_{(i,\eta)}=\delta+\eta y_i.
 \tag{38.1}
$$

As before $0^0=1$. The entire raw box is exactly

$$
 R_\nu w\le\lambda,\qquad
 w=(q_0,\ldots,q_k,f_0,\ldots,f_d)^{\mathsf T}.
 \tag{38.2}
$$

For each $m$-element subset $I$ of the ordered labels, retain its induced row order, write $R_{\nu,I}$ for the square submatrix, and form

$$
 \begin{aligned}
 \Delta_{\nu,I}&=\det R_{\nu,I},\\
 N_{\nu,I,\ell}&=
    \det\big(R_{\nu,I}\text{ with column }\ell
                                  \text{ replaced by }\lambda_I\big)
                  &&(0\le\ell<m),\\
 S_{\nu,I,r}&=
    \det\begin{pmatrix}R_{\nu,I}&\lambda_I\\
                       R_{\nu,r}&\lambda_r\end{pmatrix}
                  &&(r=(i,\eta)).
 \end{aligned}
 \tag{38.3}
$$

All these are explicit polynomials in just $\alpha,\beta$. Their coefficients are fixed by the acquired $y,\delta$, the integer clocks and actual $A_i$. In particular their generation involves no unknown source, gain coefficient, drift coefficient, or error variable.

For a fixed $I$, the **legal basis predicate** is

$$
 \begin{split}
 \Psi_{\nu,I}(\alpha,\beta):\quad&
 \Delta_{\nu,I}\ne0,\qquad
 \operatorname{sgn} S_{\nu,I,r}
       \in\{0,\operatorname{sgn}\Delta_{\nu,I}\}\quad\text{for every }r,\\
 &\text{and }N_{\nu,I,j}\ne0
                       \quad\text{for at least one }0\le j\le k.
 \end{split}
 \tag{38.4}
$$

Let $\Phi_\nu$ be the disjunction of these predicates over all $I$. Identically zero determinants can be omitted; any other identically zero polynomial retains sign zero. Signs in (38.4) are evaluated separately, so no multiplication of $\Delta$ and $S$ is required to express the test.

**Theorem 38.2 (exact elimination and degree control).** For every $\alpha,\beta>0$, $\Phi_\nu(\alpha,\beta)$ holds if and only if there is a whole legal world in $\mathcal W_\delta(y)$ with source $P_\nu(\alpha,\beta)$. If $\Psi_{\nu,I}$ holds, one such whole world is explicitly

$$
 \begin{aligned}
 P&=X_\nu/(\alpha+\beta),\\
 H(\tau)&=(\alpha+\beta)
              \sum_{j=0}^k\frac{N_{\nu,I,j}}{\Delta_{\nu,I}}\tau^j,\\
 D(\tau)&=\sum_{j=0}^d
              \frac{N_{\nu,I,k+1+j}}{\Delta_{\nu,I}}\tau^j,\qquad
 \xi_i=y_i-B_{\nu,i}Q(i)-D(i).
 \end{aligned}
 \tag{38.5}
$$

The degrees below are total degrees in the two source parameters:

| Data | Degree bound |
|---|---:|
| Gain columns of $R_\nu$ | $2$ |
| Drift columns and $\lambda$ | $0$ |
| $\Delta_{\nu,I}$, every $S_{\nu,I,r}$, and every drift numerator $N_{\nu,I,k+1+j}$ | $2(k+1)$ |
| Every gain-legality numerator $N_{\nu,I,j}$, $0\le j\le k$ | $2k$ |

There are at most

$$
                    2\binom{2L}{k+d+2}
 \tag{38.6}
$$

bases in the two charts together. This counts bases, not arithmetic operations or root samples.

**Proof.** At a nonsingular basis, Cramer's rule gives $w_\ell=N_\ell/\Delta$. The bordered determinant identity gives, for every signed raw constraint,

$$
 S_r=\Delta\lambda_r-R_r\operatorname{adj}(R_I)\lambda_I
     =\Delta(\lambda_r-R_rw).
 \tag{38.7}
$$

Thus (38.4) says exactly that this Cramer point satisfies every inequality in (38.2) and has a nonzero gain coefficient. Its source is legal by (37.1), and $(\alpha+\beta)Q\ne0$. Equations (37.3) and (38.7) verify each of the errors in (38.5) in the same whole world.

For the converse, Lemma 37.2 makes the feasible coefficient set a compact polytope. A nonempty compact polytope is the convex hull of its vertices, and at each vertex $m$ linearly independent active constraint normals can be chosen. These standard facts apply also when the polytope has smaller affine dimension. If a feasible point has $q\ne0$, at least one vertex has $q\ne0$: otherwise every convex combination of vertices would have zero gain block. Choose the independent active rows at such a vertex. Their determinant is nonzero and Cramer's rule and (38.7) give precisely (38.4). This proves necessity without replacing the strict condition $H\ne0$ by its closure. The polyhedral suppliers used here are Kaibel, *Basic Polyhedral Theory*, Theorems 2, 13 and 15, with the bounded-polyhedron specialization of the Weyl–Minkowski description; their role is the vertex/Cramer step, not the source parametrization or its escape interpretation.

For the degree statements, there are exactly $k+1$ columns depending on $\alpha,\beta$, each of degree at most two. All drift columns and the right-hand-side column are constant in these parameters. In each determinant monomial, each column occurs once. Hence $\deg\Delta\le2(k+1)$. Replacing a gain column leaves only $k$ quadratic columns, proving $\deg N_j\le2k$; replacing a drift column leaves $k+1$. The bordered determinant defining $S_r$ also has only $k+1$ quadratic columns, proving the same bound $2(k+1)$ for its degree. Estimating the two terms of (38.7) separately is unnecessary and would obscure this bound. Increasing $d$ adds only parameter-independent columns and more candidate row sets. Finally each chart has at most $\binom{2L}{m}$ choices of $I$. $\square$

Theorem 38.2 eliminates the entire original-variable coefficient vectors, rather than allowing separate values of $H$ or $D$ at different reads. It allows degree drops, gain signs, all sampled gain roots and all exact active raw equalities. It imposes no positive lower bound on the Cramer gain block. In particular along passing worlds $Q$ may tend to zero, so the $Q=0$ auxiliary limits in (30.2) are retained; only an identically zero gain in an actual positive-scale world is excluded.

## 39. A finite root-sign test at one sufficiently small scale

This section specifies the finite sign evaluation used for the determinant data. It supplies an evaluated-fiber criterion, with a proof of its uniform positive-scale meaning. No quantifier-elimination existence assertion is needed.

**Definition 39.1 (projection polynomials and the sample scale).** Collect the polynomials $\Delta_{\nu,I},N_{\nu,I,j}$ for $0\le j\le k$, and $S_{\nu,I,r}$ from both charts, including those needed in (38.4). Substitute

$$
                    \alpha=x,\qquad \beta=s-x,
 \tag{39.1}
$$

and adjoin the two boundary polynomials $x,s-x$. Call this finite family $\mathscr F\subset\mathbb R[s,x]$, keeping zero members as fixed zero signs. Its nonzero members have total degree at most $D_*=2(k+1)$.

Factor each nonzero member, over $\mathbb R[s,x]$, in the form

$$
                p(s,x)=c_p(s)\prod_{h\in\mathscr H}h(s,x)^{e(p,h)}.
 \tag{39.2}
$$

Here $c_p$ is a nonzero polynomial in $s$, the distinct $h$ that actually occur form one common list $\mathscr H$, and each $h$ is irreducible, primitive as a polynomial in $x$ over $\mathbb R[s]$, and of positive $x$ degree. Constant real factors are absorbed into $c_p$; fix any exact normalization of the factors. This is an algebraic specification with the given real coefficients, not a bit-computability assumption.

Form the finite univariate family $\mathscr P\subset\mathbb R[s]$ consisting of all $c_p$, all nonzero coefficients of each $h$ as a polynomial in $x$, and

$$
 \operatorname{Res}_x(h,\partial_xh),\qquad
 \operatorname{Res}_x(h,\widetilde h)
                         \quad(h\ne\widetilde h\text{ in }\mathscr H).
 \tag{39.3}
$$

Use the ordinary Sylvester determinants for these resultants. None of the displayed resultants is the zero polynomial: over the characteristic-zero field $\mathbb R(s)$, irreducible positive-degree $h$ is squarefree, and two distinct primitive factors are coprime. Zero coefficient polynomials are not included in $\mathscr P$. Constant nonzero polynomials have no roots.

The following positive numbers are determined by this finite data:

$$
 \zeta=\min\big(\{1\}\cup
       \{r>0:p(r)=0\text{ for some }p\in\mathscr P\}\big),\qquad
 \varepsilon=\zeta/2,\qquad s_*=\zeta/4.
 \tag{39.4}
$$

The root set is finite, so $\zeta>0$. In particular no member of $\mathscr P$ vanishes on $(0,\varepsilon)$. Roots at $s=0$ are harmless and are not included in the positive-root set.

At the one scale $s_*$, let

$$
             0=r_0<r_1<\cdots<r_a<r_{a+1}=s_*
 \tag{39.5}
$$

be the distinct roots in $(0,s_*)$ of $\prod_{h\in\mathscr H}h(s_*,x)$, together with the displayed endpoints. Take the finite sample set

$$
 \mathscr T=
       \{r_1,\ldots,r_a\}\ \cup\
       \{(r_j+r_{j+1})/2:0\le j\le a\}.
 \tag{39.6}
$$

For each chart define the Boolean number

$$
 \mathsf{Pass}_\nu(y,\delta)=
       \bigvee_{x_*\in\mathscr T}\Phi_\nu(x_*,s_*-x_*).
 \tag{39.7}
$$

Thus (39.7) requires only finitely many signs of the specified determinant polynomials at finitely many roots and intervening samples of univariate polynomials. The disjunction includes root samples as well as open intervals. In particular an exactly active equality can be the only passing possibility.

**Lemma 39.2 (why the one-scale test controls all smaller scales).** For each $\nu$, the following are equivalent:

1. $\mathsf{Pass}_\nu(y,\delta)$ is true.
2. For every $0<s<\varepsilon$, there is $0<x<s$ with $\Phi_\nu(x,s-x)$.
3. There is a sequence $s_n\downarrow0$ and $0<x_n<s_n$ with $\Phi_\nu(x_n,s_n-x_n)$.

More precisely, if (39.7) passes, a fixed basis $I$ and a continuous root section or a midpoint between two neighboring root sections can be used throughout $(0,\varepsilon)$, keeping $\Psi_{\nu,I}$ true.

**Proof.** The leading coefficient of every $h$ is among the projection polynomials. Thus its specialized $x$ degree stays fixed on $(0,\varepsilon)$. The self-resultant in (39.3) ensures that all its complex roots are simple there, and the pairwise resultants ensure that two different factors have no common root. These implications follow from the elementary Sylvester common-root criterion, with no degree loss on this interval.

For clarity, the needed real-root continuity can be proved directly on this interval. At any fixed $s_0>0$, a simple real root continues locally as a unique continuous root by the implicit function theorem. No additional real roots appear nearby: in a neighborhood of $s_0$ the leading coefficient is bounded away from zero, the other coefficients are bounded, and the elementary monic-polynomial root bound bounds all roots. A convergent subsequence of any purported additional real roots would give a root at $s_0$; simplicity and local uniqueness exclude it. Complex roots cannot become real without a multiple root. It follows that the number of real roots is locally constant, hence constant on the interval. Order the roots increasingly; their local continuations then join to global continuous sections. Pairwise nonintersection fixes the order of all sections from all factors.

The boundary factors $x$ and $s-x$ are in the same list. Hence the sections $x=0$ and $x=s$ never cross an interior section. Between them, the number and ordering of sections and sectors are fixed for every $0<s<\varepsilon$. On each section, a factor is either identically zero or nowhere zero; on each open sector every factor is nowhere zero. These cells are connected, so each nowhere-zero factor has constant sign. The vertical factors $c_p(s)$ have constant nonzero sign too. The factorization (39.2) consequently makes the signs of all original members of $\mathscr F$ constant on each of these cells. An identically zero member has sign zero throughout.

At $s_*$, (39.6) samples every interior section and every sector between the boundary sections. Thus each truth value of (38.4) found there persists on the corresponding entire cell, and every truth value at any other $s$ occurs at its matching sample. This proves the equivalence, including the sequence version. For a passing sample choose one passing basis $I$. If the sample is a root, follow that section; if it is a midpoint, use the midpoint of its two continuous boundary sections at each $s$. These choices stay in the same cell and keep every sign in $\Psi_{\nu,I}$ unchanged. $\square$

The root-sign principle is standard; the argument above gives its hypotheses explicitly for this particular bivariate projection. Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, second edition, Propositions 11.9 and 11.11, supply the general sign-invariant sampling and constant-fiber-sign framework. No assertion that a discriminant alone controls a degree-dropping or identically nullified family is used here. Primitive factorization, the vertical factors, the leading coefficients, and the boundary sections are all part of the construction.

The determinant degree bounds of Theorem 38.2 concern the eliminated source certificates. Auxiliary projection degrees can be larger. For example the Sylvester construction gives the coarse bound $2D_*^2$ on the degrees in $s$ of the polynomials in (39.3): the matrix has at most $2D_*$ rows and each entry has degree at most $D_*$. This bound too is independent of $d$; the number of polynomials and bases need not be. No runtime or optimal degree assertion is made.

## 40. Necessary and sufficient finite acquired-record criterion

**Theorem 40.1 (finite signs are equivalent to actual source escape).** Use Definitions 38.1 and 39.1 for the actual $y,\delta,k,d$ on (26.2). Then:

1. The $P_{12}$ projection of $\mathcal W_\delta(y)$ is unbounded if and only if $\mathsf{Pass}_{12}(y,\delta)$ is true. The corresponding equivalence holds for $P_{21}$ and $\mathsf{Pass}_{21}$.
2. The source projection is unbounded if and only if at least one of the two finite tests passes. A passing test constructs whole legal worlds at every $0<s<\varepsilon$, with the selected escaping entry exactly $1/s$, by the fixed-basis formulas (38.5).
3. If the $12$ test fails, every compatible world has $P_{12}\le1/\varepsilon$. If the $21$ test fails, every compatible world has $P_{21}\le1/\varepsilon$. If both fail, all compatible complete targets satisfy

$$
 \begin{aligned}
 \|P\|_{\max}&\le\max\{1,\varepsilon^{-1}\},\\
 \|\operatorname{coeff}_kH\|_\infty
                    &\le\|\widehat h\|_\infty+a\delta,\\
 \|\operatorname{coeff}_dD\|_\infty
                    &\le\|\widehat a\|_\infty+a\delta,
 \end{aligned}
 \tag{40.1}
$$

where $a,\widehat h,\widehat a$ are the unchanged original-clock prefix quantities of (26.4). Empty compatibility sets satisfy these bounds vacuously.

**Proof.** Suppose the $12$ test passes. Lemma 39.2 supplies positive $\alpha(s)=x(s)$, $\beta(s)=s-x(s)$ and one basis whose complete sign predicate holds for every $0<s<\varepsilon$. Theorem 38.2 then gives the single source and the two whole polynomials in (38.5), together with all $L$ legal raw errors, at each such $s$. Every $H$ is genuinely nonzero, since at least one of its gain Cramer numerators is nonzero at that positive scale. The source has $P_{12}=1/s$, so its projection is unbounded. In the other direction, from compatible worlds with $P_{12}\to\infty$ use their exact first-chart coordinates from Lemma 37.2. Then $s=1/P_{12}\to0$. Necessity in Theorem 38.2 gives $\Phi_{12}$ at these points, so Lemma 39.2 makes the finite test pass. The proof for $21$ is identical with the second chart.

All diagonal entries lie strictly between zero and one. Thus an unbounded set of allowed sources has an unbounded off-diagonal coordinate, and a subsequence in one of the two directions proves assertion 2. If a failed test admitted a compatible $P_{12}>1/\varepsilon$, its chart would have $0<s<\varepsilon$ and a true $\Phi_{12}$, contradicting Lemma 39.2. This proves the directional bounds, and both together give the first line of (40.1). Finally (26.9) is valid for every whole world with this same received prefix and raw radius; its $H,D$ bounds give the remaining lines. No gain lower bound is needed for boundedness of these two coefficient blocks. $\square$

This is a source-specific necessary-and-sufficient acquired-record criterion at the original radius, with all gain and drift coefficients eliminated before the two-variable sign problem. Its inputs are precisely the finite raw vector, the declared degrees, and the declared radius. Passing evidence is a whole-world formula, not independent prefix and tail feasibility. Negative evidence in both directions gives a finite source bound and the existing prefix bounds give complete-target boundedness. The finite test makes no claim that a failed record has a positive gain floor, a small recovery radius, or boundedness after any radius inflation.

**Corollary 40.2 (contact and the existing five-read consumers).** At $e(y)=\delta$, either truth value of each test in (39.7) is permitted; their disjunction settles exact-radius unboundedness. At $e(y)>\delta$ both tests fail, and at $e(y)<\delta$ at least one passes. These last two statements follow from Theorems 31.2 and 32.1 combined with Theorem 40.1.

For the very same five reads with $k=d=0$, Proposition 34.1 supplies

$$
 y^{\rm B}=(0,2,0,0,0),\qquad\delta=1:
                  \quad(\mathsf{Pass}_{12},\mathsf{Pass}_{21})
                                      =(\mathrm{false},\mathrm{false}).
 \tag{40.2}
$$

Proposition 35.1 supplies

$$
 y^{\rm U}=(1,7/10,17/10,19/10,21/10),\qquad\delta=3/5:
                  \quad(\mathsf{Pass}_{12},\mathsf{Pass}_{21})
                                      =(\mathrm{true},\mathrm{false}).
 \tag{40.3}
$$

These are applications of their existing proofs, without repeating their world constructions. The $12$ assertion in (40.3) uses its actual family (35.3). For the negative $21$ assertion, an unbounded $P_{21}$ subsequence would, by the corresponding half of the proof of Theorem 30.2, have a finite record limit in $\mathcal E_{21}$ inside the closed radius-$3/5$ box. Its distance is $7/10>3/5$, which excludes that subsequence. Thus the finite criterion consumes both opposite exact-radius examples, including the zero auxiliary polynomial allowed in their limit spaces.

## 41. Nonempty bounded contact with nonzero auxiliary gains

**Proposition 41.1.** On exactly (29.1), let $k=d=0$ and

$$
               y^{\rm E}=(0,5/2,3/2,1/2,3/2),\qquad\delta=1.
 \tag{41.1}
$$

Then $\mathcal W_1(y^{\rm E})$ is nonempty,

$$
 \operatorname{dist}_\infty(y^{\rm E},\mathcal E_{12})=1,\qquad
 \operatorname{dist}_\infty(y^{\rm E},\mathcal E_{21})=9/8.
 \tag{41.2}
$$

Every approximant in $\mathcal E_{12}$ within radius one has

$$
                F\in[1/2,1],\qquad Q=3/2-F\in[1/2,1].
 \tag{41.3}
$$

Nevertheless every actual compatible source is bounded. More explicitly, for all compatible whole worlds,

$$
 b\le5/6,\qquad \|P\|_{\max}\le1,\qquad
                  -3\le h\le-1/2,\qquad -1/2\le D\le4.
 \tag{41.4}
$$

Both finite tests of Theorem 40.1 therefore fail.

**Proof.** Nonemptiness is witnessed by

$$
 P=\begin{pmatrix}99/100&9/100\\11/100&1/100\end{pmatrix},
                  \qquad H=-1,\qquad D=2.
 \tag{41.5}
$$

The source is strictly positive, trace one and determinant zero. Using the same triple at all five original clocks, (29.5) gives the noiseless vector

$$
                  z=(1,179/100,79/100,69/100,69/100).
$$

The errors $y^{\rm E}-z=(-1,71/100,71/100,-19/100,81/100)$ all have magnitude at most one.

For $\mathcal E_{12}$, coordinates $1$ and $3$ of every approximant are equal. Their received difference is two, proving the lower bound one. At radius one their common value must be $3/2$, hence $F+Q=3/2$. The clock-$0$ constraint gives $F\in[-1,1]$, and the clock-$4$ constraint gives $3-F\in[1/2,5/2]$. These are exactly $F\in[1/2,1]$; the clock-$2$ constraint is then automatic. This proves attainability and the entire nonzero contact-gain interval (41.3).

For $\mathcal E_{21}$ every approximant $w$ satisfies $2w_1-w_0-w_3=0$. Its value on $y^{\rm E}$ is $9/2$, and the sum of the absolute coefficients of this functional is four, giving distance at least $9/8$. The choice $F=9/8,Q=1/4$ has residual

$$
 y^{\rm E}-(F+VQ)=(-9/8,9/8,1/8,-9/8,1/8),
$$

and attains the bound.

For actual compatibility, use $P$ as in (30.5) and one whole $h\ne0,D$. The constraints give $z_3\le3/2\le z_1$. But the exact same-source contrast in (29.5) is

$$
                 z_3-z_1=h(1+v-t).
 \tag{41.6}
$$

Its factor is strictly positive, so $h<0$. Also $z_1-z_0\ge1/2$, whence

$$
                (-h)(1-b)=h(b-1)=z_1-z_0\ge1/2.
 \tag{41.7}
$$

Since $b>0$ and $h=z_2-z_1\ge(1/2)-(7/2)=-3$, it follows that $-h\ge1/2$ and $1-b\ge1/6$. This proves the stated gain and $b$ bounds. The diagonal entries are below one and both off-diagonal entries are below $b$, giving the source bound. Finally $D=z_0-h$, $z_0\in[-1,1]$, gives its interval in (41.4). This nonempty bounded contact does not rely on an auxiliary contact gain vanishing. $\square$

## 42. Arbitrarily late positive violation on legal escaping worlds

**Proposition 42.1 (exact remainder beyond every prescribed weak Taylor depth).** Retain the single record $y^{\rm E}$ and radius one of (41.1). For each integer $n\ge0$, put $m=\max\{1,n\}$. There is a family of legal whole worlds, at the same five original clocks, indexed by $0<r\le1/8$, with $\|P_r\|_{\max}=1/r$, such that the only violated raw constraint is at clock $3$ and its exact excess over radius one is

$$
       \eta_m(r)=\frac34 r^{m+1}(1+r-r^{m+1})>0.
 \tag{42.1}
$$

In particular every signed raw slack has a Taylor expansion at $r=0$ whose first nonzero coefficient through order $n$, if there is one, is nonnegative. The clock-$3$ slack vanishes through order $n$, yet is strictly negative at every positive $r$. All the worlds are compatible at radius $1+\eta_m(r)$, and none is compatible at radius one.

**Proof.** Set

$$
 \begin{gathered}
 t_r=1-r^m,\qquad u_r=r^{-1},\qquad
 v_r=r\,t_r(1-t_r),\\
 P_r=\begin{pmatrix}1-t_r&u_r\\v_r&t_r\end{pmatrix},\qquad
 h_r=\frac34r,\qquad b_r=u_r+v_r+t_r,\qquad
 D_r=\frac32-h_rb_r.
 \end{gathered}
 \tag{42.2}
$$

For every positive parameter in the stated interval, all source entries are positive, the trace is one, and $u_rv_r=t_r(1-t_r)$ gives determinant zero. Its largest entry is $1/r$. The one whole constant gain $h_r$ is nonzero and the one whole constant drift is $D_r$. Substitution into all five reports, without a truncated expansion, gives

$$
 \begin{aligned}
 z_0&=\frac34+\frac34r^{m+1}
                         -\frac34r^{m+2}(1-r^m),\\
 z_1&=\frac32,\\
 z_2&=\frac32+\frac34r,\\
 z_3&=\frac32+\frac34r^{m+1}(1+r-r^{m+1}),\\
 z_4&=\frac94+\frac34r(2-r^m).
 \end{aligned}
 \tag{42.3}
$$

Here $z_3-z_1=h_r(1+v_r-t_r)$ is the same exact contrast as (41.6). For $r\le1/8$, $3/4\le z_0\le3/4+3/256<1$, $z_2\in[3/2,51/32]$, and $9/4\le z_4\le39/16<5/2$. These prove all raw constraints except clock $3$; clock $1$ is exactly active with $y_1-z_1=1$. At clock $3$, $z_3-y_3=1+\eta_m(r)$, where the factor in (42.1) is positive. The remaining signed constraint at that clock has slack $2+\eta_m(r)>0$.

The reports and their signed slacks are polynomials in $r$ and extend to $r=0$. Every slack except the active clock-$1$ slack and the violating clock-$3$ slack has a strictly positive constant term. The clock-$1$ active slack is identically zero; the violating clock-$3$ slack is exactly

$$
 1-(z_3-y_3)
       =-\frac34r^{m+1}
        -\frac34r^{m+2}
        +\frac34r^{2m+2}
       =-\frac34r^{m+1}+O(r^{m+2}).
 \tag{42.4}
$$

Thus its coefficients through the prescribed depth $n\le m$ are all zero, with a strictly negative leading coefficient at the next displayed order. Formula (42.4), together with the positive exact factor in (42.1), specifies both the remainder and its sign for the whole positive interval; it is not a claim inferred from a finite truncation. This proves every assertion. $\square$

The auxiliary $12$ gain in this family is $u_rh_r=3/4$, and $D_r\to3/4$, an interior point of (41.3). In chart (37.1) its exact source parameters are

$$
              \alpha=r^{m+1},\qquad
              \beta=r-r^{m+1},\qquad s=r.
 \tag{42.5}
$$

The endpoint ratio $t_r=\beta/s$ therefore approaches one at an arbitrary prescribed polynomial rate, while the escaping entry is always $1/r$. This exhibits why weak nonnegative finite jets along a proposed family cannot by themselves certify exact-radius compatibility: a strictly negative slack can first appear beyond that chosen depth even with nonzero limiting auxiliary gain. It does not contradict effective finite-order bounds obtained using the full polynomial system and correctly selected algebraic cells. Theorem 40.1 uses that full system and exact signs; it does not promote the weak jets of these deliberately chosen arcs into passing evidence.

## 43. Mathematical suppliers and the precise scope of the finite criterion

The source contract and paid trajectory remain Definitions 25.1, 26.1 and 30.1. Main [*FIB Self-Calibrating Relation Mathematics*, Definition 39.1 and Theorem 39.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md#39-任意已知有限次共同增益的零安全固定历史恢复), through the already instantiated inverse (26.4), supply coefficient-fiber injectivity and the two complete-target coefficient bounds. The existing moving-trace identities (29.5) supply the exact five-read contrasts. Propositions 34.1 and 35.1 supply the two previously established contact consumers. None of their proofs or acquisition budgets is replaced.

Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorems 2, 8, 13 and 15](https://arxiv.org/abs/1001.2161v1), supplies Cramer's rule, finite polyhedral descriptions, the independent-active-row description of vertices and the convex-hull description for bounded polyhedra used in Theorem 38.2. These standard tools do not supply (37.1)–(37.3), the gain-only degree accounting, or the same-world equivalence.

Saugata Basu, Richard Pollack and Marie-Françoise Roy, [*Algorithms in Real Algebraic Geometry*, second edition, Propositions 11.9 and 11.11, printed pp. 417 and 419](https://www.maths.ed.ac.uk/~v1ranick/papers/basupollackroy.pdf), supply the mature sign-invariant sampling framework. Marc Moreno Maza's university notes, [*The resultant*, Definition 4 and Propositions 5–6](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html), supply the Sylvester determinant and coprimality criterion used in (39.3). Lemma 39.2 explicitly checks the squarefreeness, specialization, boundary and nonintersection hypotheses needed here and proves the resulting root-section argument. No weakened delineability hypothesis is assumed. The abstract real-algebraic decision policy in *FIB Self-Calibrating Relation Mathematics IV*, Corollary 9.4, is not counted as new mathematical content.

The additional source-specific content is the exact two-parameter polynomial chart with the whole gain and drift still linear; elimination to the signed basis family (38.3)–(38.4); degree bounds depending on gain degree alone; the explicit one-scale sign construction with its legal-whole-world reconstruction and two-direction negative bound; and the nonzero-gain bounded contact with its arbitrarily delayed exact violation family. These are deductions for the given source and acquired-record model using the credited intermediate tools, without an external priority claim.

The criterion covers every declared $k,d\ge0$, every received real vector and nonnegative radius, and in particular the full exact-radius contact set. It neither changes the reading contract nor strengthens the world class. It keeps zero auxiliary limits, genuine nonzero actual gains, roots and degree drops, exact active equalities and endpoint ratios at arbitrary rates. It does not substitute the exact-ancestor/corridor contracts in volume IX or the affine six-read recorded-clock contracts for this all-raw original-clock model. Finite real sign and root data do not assert finite-bit computability for arbitrary real presentations, an acquisition root oracle, runtime efficiency, optimal complexity or constants, physical realization, literature priority, or Lean kernel certification. Boundedness at the exact radius and boundedness after positive inflation remain different properties.

## 追加锚（本行以下为增补区）

## 44. Exact drift elimination with a fixed number of joint error coordinates

Throughout §§44–48 the contract is exactly Definitions 25.1, 26.1 and 30.1. Fix arbitrary $k,d\ge0$, the $L=3k+d+5$ paid clocks and matrices of (26.2), $y\in\mathbb R^L$ and $\delta\ge0$. Use both source charts $P_\nu=X_\nu/(\alpha+\beta)$ of (37.1), with $\alpha,\beta>0$, and their exact trace numerators $B_{\nu,i}$ in (37.2). Write

$$
 p=k+1,\qquad r=L-d-1=3k+4.
 \tag{44.1}
$$

Here $p$ is the number of gain coefficients and $r$ is the codimension of the sampled drift space. In particular $r$ does not increase with $d$. The source is a real entrywise-positive rank-one matrix; no symmetry or Hermitian positivity is assumed. These sections replace the exponentially many raw coefficient bases in (38.6) by an explicitly counted family polynomial in $d$ for each fixed $k$. They do not change the compatibility set or the exact-radius escape question.

**Definition 44.1 (weighted moments of the original error vector).** For the original integer clocks, put

$$
 \omega_i=\frac1{\prod_{0\le j<L,\ j\ne i}(i-j)}
          =\frac{(-1)^{L-1-i}}{i!(L-1-i)!},\qquad
 W_{ai}=\omega_i i^a\quad(0\le a<r),
 \qquad g_i=W_{\bullet i}.
 \tag{44.2}
$$

Thus $W$ has $r$ rows and all $L$ raw-error coordinates as columns. Define

$$
 b=Wy,\qquad
 C_{\nu,aj}(\alpha,\beta)
       =\sum_{i=0}^{L-1}\omega_i i^{a+j}B_{\nu,i}(\alpha,\beta)
                  \quad(0\le j<p),\qquad
 Z_\delta=W[-\delta,\delta]^L.
 \tag{44.3}
$$

All weights and clocks in this definition are fixed. $b$ is not the scalar $\operatorname{tr}(MP)$ used in earlier sections. No processed coordinate of $W\xi$ is assigned an independent error allowance: $Z_\delta$ is the image of one common raw-error box.

**Theorem 44.2 (same-world reduction and explicit error geometry).** For any fixed chart and positive $\alpha,\beta$, the original compatible worlds at that source correspond exactly to pairs $(q,\xi)$ satisfying

$$
 q\in\mathbb R^p\setminus\{0\},\qquad
 |\xi_i|\le\delta\ (0\le i<L),\qquad
 C_\nu q+W\xi=b.
 \tag{44.4}
$$

The correspondence sets $Q(\tau)=\sum_{j=0}^{p-1}q_j\tau^j$, $H=(\alpha+\beta)Q$ and obtains the unique whole $D\in\Pi_d$ by interpolation of

$$
 R_i=y_i-B_{\nu,i}Q(i)-\xi_i.
 \tag{44.5}
$$

Consequently the allowed gain vectors, before imposing $q\ne0$, form the empty or compact polytope

$$
 K_\nu(\alpha,\beta)=\{q:b-C_\nu q\in Z_\delta\}.
 \tag{44.6}
$$

The following concrete lists describe the error geometry, with no dependence on source parameters. For every $(r-1)$-element subset $J\subset\{0,\ldots,L-1\}$, define the coefficient vector $n_J\in\mathbb R^r$ and positive scalar $h_J$ by

$$
 \rho_J(\tau)=\prod_{j\in J}(\tau-j)
             =\sum_{a=0}^{r-1}(n_J)_a\tau^a,
 \qquad h_J=\sum_{i=0}^{L-1}|\omega_i\rho_J(i)|.
 \tag{44.7}
$$

Then, including $\delta=0$,

$$
 t\in Z_\delta
 \quad\Longleftrightarrow\quad
       \eta n_J^{\mathsf T}t\le\delta h_J
       \quad\text{for every }(J,\eta),\quad \eta\in\{+1,-1\}.
 \tag{44.8}
$$

There are

$$
 F=2\binom{L}{r-1}
 \tag{44.9}
$$

signed facet labels. For a second list let $G\subset\{0,\ldots,L-2\}$ have at most $r-1$ elements and let $\epsilon\in\{+1,-1\}$. Define

$$
 \sigma_i^{\epsilon,G}
    =\operatorname{sgn}(\omega_i)\epsilon
                    (-1)^{|\{j\in G:j<i\}|},\qquad
 v_{\epsilon,G}=W\sigma^{\epsilon,G}.
 \tag{44.10}
$$

These are precisely the distinct vertices of $Z_1$. In particular

$$
 Z_\delta=\delta\operatorname{conv}\{v_{\epsilon,G}\},\qquad
 V=2\sum_{j=0}^{r-1}\binom{L-1}{j}
 \tag{44.11}
$$

is the vertex count for $Z_1$, even though $Z_0=\{0\}$. $F$ and $V$ count labels and vertices, respectively, not arithmetic operations.

**Proof.** The Lagrange formula with the weights (44.2) gives

$$
 \sum_{i=0}^{L-1}\omega_i i^m=0\quad(0\le m\le L-2).
 \tag{44.12}
$$

Indeed interpolate $\tau^m$ at all $L$ clocks and compare the coefficient of $\tau^{L-1}$. This is an immediate use of the standard Lagrange formula and barycentric weights in Berrut–Trefethen, equations (2.1) and (3.2), rather than a new interpolation theorem. Since $(r-1)+d=L-2$, $W$ annihilates every sampled polynomial in $\Pi_d$. Any $r$ columns of $W$ are independent: their determinant is a nonzero product of the selected weights and a Vandermonde determinant at distinct clocks. Thus $\operatorname{rank}W=r$, and dimension gives

$$
 \ker W=\{(D(i))_{i=0}^{L-1}:D\in\Pi_d\}.
 \tag{44.13}
$$

Applying $W$ to the original equation (37.3) with raw errors gives (44.4). Conversely (44.4) makes (44.5) lie in this kernel, so it is the evaluation vector of one unique polynomial of degree at most $d$. Interpolation at the fixed clocks $0,\ldots,d$ recovers that polynomial, and (44.13) makes it agree at every remaining paid clock. This proves the exact correspondence, not just separate gain and drift feasibility. It includes every original $(P,H,D,\xi)$ by taking its own $q=\operatorname{coeff}(H)/(\alpha+\beta)$ and its own error vector.

Equation (44.6) follows by projecting over that common box. It is exactly the projection onto $q$ of the coefficient polytope in Lemma 37.2. Hence it is compact when nonempty. Equivalently, $C_\nu$ is injective: $C_\nu q=0$ would make $B_\nu Q$ a sampled drift polynomial by (44.13), contradicting (37.4) unless $q=0$. This also directly bounds the inverse image of the bounded set $b-Z_\delta$.

For completeness the required finite-dimensional polyhedral steps are standard: a polytope is the intersection of its facet halfspaces and the convex hull of its vertices. They are used here in their real-coefficient form, as in Kaibel's polyhedral structure and face results. Their particular normals and vertices in (44.7) and (44.10) can be determined directly. For any direction $n$, maximizing $n^{\mathsf T}W\xi$ over $[-1,1]^L$ fixes $\xi_i=\operatorname{sgn}(n^{\mathsf T}g_i)$ when this scalar is nonzero and leaves the other coordinates free. The exposed face is therefore a translate of the sum of the segments $[-g_i,g_i]$ on which $n^{\mathsf T}g_i=0$. Its dimension is the rank of those generators.

A nonzero $n$ corresponds to the polynomial $\rho(\tau)=\sum_{a<r}n_a\tau^a$. It annihilates $g_i$ exactly when $\rho(i)=0$, and so annihilates at most $r-1$ generators. Every such set is independent. A facet has dimension $r-1$, so its zero set has exactly $r-1$ clocks and its polynomial is a nonzero scalar multiple of $\rho_J$. Conversely each $J$ in (44.7) gives such a facet. Its two support constants are exactly $h_J$. This proves (44.8) for $\delta>0$.

For $\delta=0$, both signs in (44.8) imply $n_J^{\mathsf T}t=0$ for every $J$. These $n_J$ span $\mathbb R^r$: choose any $r$ clocks and delete each one in turn; the resulting $r$ polynomials $\rho_J$ are nonzero at their respective omitted clock and zero at the others, hence are independent. Thus $t=0$, proving the zero-radius case without dividing by $\delta$.

A vertex of the full-dimensional $Z_1$ has an exposing direction off all finitely many hyperplanes $n^{\mathsf T}g_i=0$: its strict exposing directions contain an open set, and a finite union of proper hyperplanes cannot fill that set. For such a direction its unique box maximizer has signs $\operatorname{sgn}(\omega_i)\operatorname{sgn}(\rho(i))$. The sequence $\operatorname{sgn}(\rho(i))$ changes sign at most $r-1$ times, since every change requires a distinct real root between adjacent clocks. This gives (44.10).

Conversely, for every displayed $(\epsilon,G)$ the polynomial

$$
 \rho_{\epsilon,G}(\tau)
       =\epsilon(-1)^{|G|}
                   \prod_{j\in G}(\tau-j-1/2)
 \tag{44.14}
$$

has precisely those nonzero sample signs and has degree at most $r-1$. Its direction uniquely maximizes the box at $\sigma^{\epsilon,G}$, so its image is an exposed vertex. Two different sign vectors in this list cannot have the same image: the direction exposing the first uniquely maximizes on the entire box, and would also maximize at the second if their images agreed. Counting the initial sign and the change locations proves (44.11). No list of all $2^L$ box corners is generated by the construction. $\square$

## 45. Polynomially many source certificates with one reconstructed raw witness

**Definition 45.1 (reduced signed bases).** Order the $F$ labels $\ell=(J,\eta)$ of (44.9) in any fixed order. For each chart define

$$
 A_{\nu,\ell}=-\eta n_J^{\mathsf T}C_\nu,
 \qquad \lambda_\ell=\delta h_J-\eta n_J^{\mathsf T}b.
 \tag{45.1}
$$

These are a row of length $p$ and a scalar. Equations (44.6) and (44.8) give exactly $K_\nu=\{q:A_\nu q\le\lambda\}$. For every $p$-element row subset $I$, in induced order, define

$$
 \begin{aligned}
 \Delta_{\nu,I}&=\det A_{\nu,I},\\
 N_{\nu,I,j}&=\det(A_{\nu,I}\text{ with column }j
                                \text{ replaced by }\lambda_I)
                                             &&(0\le j<p),\\
 S_{\nu,I,\ell}&=
       \det\begin{pmatrix}A_{\nu,I}&\lambda_I\\
                           A_{\nu,\ell}&\lambda_\ell\end{pmatrix}.
 \end{aligned}
 \tag{45.2}
$$

These symbols are the reduced data of this section, not the raw data of (38.3). The reduced predicate is

$$
 \begin{split}
 \Theta_{\nu,I}:\quad&\Delta_{\nu,I}\ne0,\qquad
          N_{\nu,I,j}\ne0\text{ for at least one }j<p,\\
 &\operatorname{sgn}S_{\nu,I,\ell}
        \in\{0,\operatorname{sgn}\Delta_{\nu,I}\}
                   \quad\text{for every }\ell.
 \end{split}
 \tag{45.3}
$$

A second finite label selects a common raw witness. Order the $V$ vertices of (44.10). Let $T=(t_0,\ldots,t_r)$ be an increasing $(r+1)$-element subset of that list, and set

$$
 E_T=\begin{pmatrix}1&\cdots&1\\v_{t_0}&\cdots&v_{t_r}\end{pmatrix},
 \qquad c_T=\det E_T.
 \tag{45.4}
$$

Retain just the subsets with $c_T\ne0$; call their number $\mathcal T$. In particular $1\le\mathcal T\le\binom V{r+1}$. These constant matrices depend only on $k,d$. For each $(\nu,I,T)$ form the $r+1$ scalar polynomials

$$
 \begin{aligned}
 u_{\nu,I}&=\Delta_{\nu,I}b-C_\nu N_{\nu,I},\\
 M_{\nu,I,T,a}&=
   \det\left(E_T\text{ with column }a\text{ replaced by }
                  \binom{\delta\Delta_{\nu,I}}{u_{\nu,I}}\right)
                                     \quad(0\le a\le r).
 \end{aligned}
 \tag{45.5}
$$

Here $N_{\nu,I}$ is the column of the $p$ gain numerators. The **complete certificate predicate** is

$$
 \Xi_{\nu,I,T}:\quad\Theta_{\nu,I}\quad\text{and}\quad
 \operatorname{sgn}M_{\nu,I,T,a}
       \in\{0,\operatorname{sgn}(c_T)\operatorname{sgn}(\Delta_{\nu,I})\}
                                     \quad(0\le a\le r).
 \tag{45.6}
$$

All predicates involve only signs of explicit polynomials in $\alpha,\beta$ with coefficients determined by the given record, radius and paid history. A zero polynomial has sign zero. Neither factoring nor any determinant inversion is imposed on an unknown actual gain value.

**Theorem 45.2 (exact source certificates and reconstruction).** At every $\alpha,\beta>0$, for either chart, the following are equivalent:

1. There is an original compatible whole world at $P_\nu(\alpha,\beta)$.
2. $\Theta_{\nu,I}$ holds for some $I$.
3. $\Xi_{\nu,I,T}$ holds for some $(I,T)$.

A passing complete certificate explicitly supplies one actual world and every original raw error. Suppress the fixed labels in the formulas and put

$$
 \begin{aligned}
 q_j&=N_j/\Delta,&
 \mu_a&=M_a/(c_T\Delta),\\
 \xi_i&=\sum_{a=0}^r\mu_a\sigma_i^{t_a},&
 Q(\tau)&=\sum_{j=0}^{p-1}q_j\tau^j,\\
 R_i&=y_i-B_{\nu,i}Q(i)-\xi_i,&
 D(\tau)&=\sum_{j=0}^dR_j
             \prod_{\substack{0\le h\le d\\h\ne j}}
                       \frac{\tau-h}{j-h},\\
 P&=X_\nu/(\alpha+\beta),&H&=(\alpha+\beta)Q.
 \end{aligned}
 \tag{45.7}
$$

Empty products are one. These formulas use the fixed original clocks, one polynomial $Q$, one polynomial $D$, and one $L$-component raw error vector. The interpolation nodes are fixed, so there is no additional node-selection label.

**Proof.** By Theorem 44.2, assertion 1 is equivalent to $K_\nu$ containing a nonzero vector. At a nonsingular reduced basis, Cramer's rule and the bordered determinant identity give

$$
 q=N/\Delta,\qquad
 S_\ell=\Delta(\lambda_\ell-A_{\nu,\ell}q).
 \tag{45.8}
$$

Thus (45.3) is exactly feasibility and nonzero gain for that vector. If a compact polytope contains a nonzero vector, at least one vertex is nonzero, since it is the convex hull of its vertices. At that vertex $p$ independent active rows exist, also for a lower-dimensional polytope. Applying these standard vertex facts (Kaibel, Theorems 13 and 15) to (44.6) proves $1\Longleftrightarrow2$. No assumption of an interior fiber has entered.

It remains to produce the joint lift rather than just invoke its existence. For any $t\in Z_\delta$, there is a retained $T$ with

$$
 \binom\delta t=E_T\mu,\qquad \mu_a\ge0.
 \tag{45.9}
$$

For $\delta>0$, (44.11) expresses $t/\delta$ as a convex combination of vertices. The elementary affine-dependence elimination underlying Carathéodory's theorem reduces its nonzero coefficients to an affinely independent subset of at most $r+1$ vertices: if the current support is dependent, take a nonzero relation $\sum a_jv_j=0$, $\sum a_j=0$, and subtract the largest multiple of this relation that keeps all weights nonnegative; at least one positive weight vanishes. Iterate until independence. Since $Z_1$ is full-dimensional, extend that independent subset to $r+1$ independent vertices, assigning zero weights to added vertices. Multiplying the weights by $\delta$ gives (45.9). This is the classical convex version of the standard conic reduction in Kaibel, Theorem 4, applied to $(1,v_j)$. For $\delta=0$, $t=0$, and any retained $T$ with $\mu=0$ works. In particular this proof introduces no division by the noise radius or full-dimensionality assumption on the original compatibility fiber.

Apply (45.9) to $t=b-C_\nu N/\Delta$ for a passing reduced basis. Cramer's rule for the constant matrix $E_T$ gives exactly $\mu_a=M_a/(c_T\Delta)$; their nonnegativity is exactly (45.6). This proves $2\Longrightarrow3$, including active zero weights. Conversely a complete certificate supplies

$$
 \sum_a\mu_a=\delta,\qquad
 W\xi=\sum_a\mu_av_{t_a}=b-C_\nu q,\qquad
 |\xi_i|\le\sum_a\mu_a=\delta.
 \tag{45.10}
$$

Theorem 44.2 now proves that the single interpolated $D$ in (45.7) has the values $R_i$ at all $L$ clocks. Equations (37.3) and (45.7) therefore give

$$
 y_i=H(i)\operatorname{tr}(A_iP)+D(i)+\xi_i
                         \quad(0\le i<L)
 \tag{45.11}
$$

in one and the same world. At least one $N_j$ is nonzero, so $Q$ and $H$ are nonzero whole polynomials. This proves $3\Longrightarrow1$ with the promised explicit reconstruction.

For necessity, start with any original compatible world, take its exact chart coordinates from Lemma 37.2, and apply (44.4) to its own whole polynomials and original errors. It yields a nonzero feasible $q$ in this very fiber; the vertex and simplex arguments then give a passing certificate at the identical source. The selected world may be another witness in the same fiber; the test excludes no original compatible source or world on account of its gain sign, degree, roots or coefficient size. The exact correspondence (44.4) retains the original world itself before witness selection. The finite certificate family decides existence and supplies a witness; it is not asserted to list each continuum of worlds individually. $\square$

## 46. Explicit degree, label and sign counts, and both escape directions

**Theorem 46.1 (polynomial certificate accounting).** With $p,r,L,F,V$ as above, put

$$
 B_0=\binom Fp,\qquad T_0=\binom V{r+1},\qquad
 \mathcal B=2B_0T_0.
 \tag{46.1}
$$

There are at most $2B_0$ reduced basis labels and at most $\mathcal B$ complete certificate labels over both charts. The latter includes every additional raw-witness simplex selection; singular constant simplices and identically singular bases can be omitted. No other reconstruction enumeration is needed. For fixed $k$,

$$
 \mathcal B=O_k\!\left((d+1)^{(r-1)(p+r+1)}\right)
           =O_k\!\left((d+1)^{12k^2+30k+18}\right).
 \tag{46.2}
$$

These are counts of candidate certificates, not runtime, arithmetic or bit complexity bounds, and not optimality assertions. The displayed binomial expressions are explicit bounds for every $k,d\ge0$, not just asymptotic bounds.

All source-dependent scalar data needed for the complete predicates have total degree at most $D_0=2p=2(k+1)$ in $\alpha,\beta$. More precisely:

| Scalar data | Source degree bound |
|---|---:|
| Entries of $C_\nu$ and $A_\nu$ | $2$ |
| $\lambda_\ell$, entries of $E_T$, and $c_T$ | $0$ |
| $\Delta_{\nu,I}$ and $S_{\nu,I,\ell}$ | $2p$ |
| Gain numerator $N_{\nu,I,j}$ | $2(p-1)$ |
| Components of $u_{\nu,I}$ and witness numerators $M_{\nu,I,T,a}$ | $2p$ |

Each reconstructed error and each coefficient of $D$ admits denominator $c_T\Delta$ and a numerator of degree at most $2p$. Each coefficient of $H$ admits denominator $\Delta$ and numerator of degree at most $2p-1$. The source uses just the original numerator matrix $X_\nu$ and positive denominator $\alpha+\beta$.

Here are explicit bounds on the data feeding §39. Count polynomial occurrences conservatively, even when different labels give identical polynomials, and set

$$
 \begin{aligned}
 \mathcal N&=2B_0\bigl[1+p+F+(r+1)T_0\bigr]+2,\\
 h_0&=D_0\mathcal N,\\
 P_0&=\mathcal N+(D_0+2)h_0+\binom{h_0}{2},\\
 E_0&=2D_0^2,\qquad S_0=2D_0h_0+1.
 \end{aligned}
 \tag{46.3}
$$

The following counts suffice:

| Count | Meaning and upper bound |
|---|---|
| Bivariate sign data | $\mathcal N$ members: all $\Delta,N,S,M$ and the two boundaries after $\alpha=x,\beta=s-x$ |
| Distinct primitive positive-$x$ factors | at most $h_0$ |
| Univariate projection data | at most $P_0$ polynomials of degree at most $E_0$ |
| Positive projection roots, counted with repetition over polynomials | at most $E_0P_0$ |
| Interior roots at the one scale $s_*$ | at most $D_0h_0$ |
| Root and intervening-sector samples | at most $S_0$ |
| Evaluations of original bivariate polynomial signs | at most $\mathcal N S_0$ |
| Complete-label/sample pairs, if all predicates are evaluated | at most $\mathcal B S_0$ |

The signs of nonzero constants $c_T$ can be fixed once for at most $T_0$ labels, shared between the charts. They do not require source-dependent sign samples. The disjunction over nonzero gain coordinates in (45.3) uses the already counted $p$ numerators; choosing the first nonzero one adds no witness enumeration. Each reconstructed target has $4+p+(d+1)$ scalar entries or coefficients, and the construction explicitly returns its $L$ raw errors, together with $r+1$ auxiliary weights. None is a new measurement. Every count in (46.1) and (46.3) is polynomial in $d$ for fixed $k$.

**Proof.** There are $F$ signed rows of length $p$, so the reduced basis count is $\binom Fp$ per chart. The entire vertex list is (44.10), and every raw lift in the proof of Theorem 45.2 uses one of at most $\binom V{r+1}$ constant matrices, in canonical vertex order. In particular there are no uncounted $2^L$ signs of active raw inequalities, no selected drift interpolation nodes, and no further coefficient bases behind the reconstruction. Since $F,V=O_k(L^{r-1})$, the two choices have exponents $p(r-1)$ and $(r+1)(r-1)$, giving (46.2); $L=d+3k+5\le(3k+5)(d+1)$.

Each column of $C_\nu$ is a fixed weighted sum of the quadratic polynomials $B_{\nu,i}$. Thus all $p$ columns of $A_\nu$ are quadratic and the right-hand side is source-independent. Multilinearity of determinants gives degree $2p$ for $\Delta$ and $S$, and degree $2(p-1)$ for $N_j$, since one quadratic column is replaced by a constant. Hence $\Delta b-C_\nu N$ has degree at most $2p$. The matrix $E_T$ is constant and only its replaced column depends on source parameters, so every $M_a$ has that same bound. Formula (45.7) gives a common numerator for the residual values

$$
 c_T\Delta y_i
   -c_T B_{\nu,i}\sum_{j<p}N_j i^j
   -\sum_{a=0}^r M_a\sigma_i^{t_a}.
 \tag{46.4}
$$

Its degree is at most $2p$. Fixed-node interpolation is linear in these values, giving the asserted degree for the drift coefficients. Multiplying $N_j$ by $\alpha+\beta$ gives the gain bound. No degree grows with $d$.

For the sign count, each of the $2B_0$ bases uses one $\Delta$, $p$ gain numerators, $F$ bordered slacks and at most $(r+1)T_0$ lift numerators. Add the two boundaries. Substitution $\alpha=x,\beta=s-x$ does not increase total degree. Factor the nonzero polynomials exactly as in (39.2), retaining zero members as fixed zero signs. There are at most $D_0\mathcal N=h_0$ distinct positive-$x$ factors, each of total degree at most $D_0$. There is at most one vertical content per original polynomial, at most $D_0+1$ nonzero coefficient polynomials per factor, one self-resultant per factor, and one resultant per unordered pair of factors. This gives $P_0$. All contents and coefficients have degree at most $D_0$; a Sylvester matrix here has at most $2D_0$ rows with entries of degree at most $D_0$, giving the conservative uniform bound $E_0$. Nonzero constant polynomials and roots at zero add no positive roots. At the selected positive scale each factor has at most $D_0$ roots, so there are at most $D_0h_0$ interior roots and $2D_0h_0+1$ section/sector samples. Counting signs and label/sample pairs proves the table. These deliberately coarse bounds require no factorization or evaluation cost hypothesis. $\square$

**Definition 46.2 (the polynomial-size escape test).** Use the bivariate family in (46.3) in place of the raw determinant family in Definition 39.1. Include $x,s-x$, all vertical contents and coefficient projections, and the self and pairwise resultants as there. Use one resultant per unordered pair, since reversing its order changes only a constant sign. Define $\zeta,\varepsilon,s_*$ and the root/sector sample set $\mathscr T$ by (39.4)–(39.6) for this family. Put

$$
 \widehat{\mathsf{Pass}}_\nu(y,\delta)
    =\bigvee_{x_*\in\mathscr T}
       \bigvee_{I,T}\Xi_{\nu,I,T}(x_*,s_*-x_*).
 \tag{46.5}
$$

The hat distinguishes this data family and its possibly different $\varepsilon$ from the original family. Both tests concern the same original radius.

**Theorem 46.3 (unchanged exact-radius escape decision and negative bounds).** For every $k,d\ge0$, every $y$ and every $\delta\ge0$:

$$
 \widehat{\mathsf{Pass}}_\nu(y,\delta)
          =\mathsf{Pass}_\nu(y,\delta)
          \quad(\nu=12,21).
 \tag{46.6}
$$

In particular the $P_{12}$ source projection is unbounded exactly when the new $12$ test passes, and the same equivalence holds for $21$. A passing label and root section or sector midpoint in (46.5), fixed over all $0<s<\varepsilon$, together with (45.7), constructs legal whole worlds at every such scale with the selected entry exactly $1/s$. A failed $\nu$ test bounds that entry by $1/\varepsilon$ in every compatible world. If both fail, all compatible targets satisfy

$$
 \begin{aligned}
 \|P\|_{\max}&\le\max\{1,\varepsilon^{-1}\},\\
 \|\operatorname{coeff}_kH\|_\infty
                   &\le\|\widehat h\|_\infty+a\delta,\\
 \|\operatorname{coeff}_dD\|_\infty
                   &\le\|\widehat a\|_\infty+a\delta,
 \end{aligned}
 \tag{46.7}
$$

with exactly the unchanged $a,\widehat h,\widehat a$ of (26.4). Empty compatibility sets are included.

**Proof.** Theorem 45.2 identifies $\bigvee_{I,T}\Xi_{\nu,I,T}$ with $\Phi_\nu$ at every positive source coordinate, including all equalities and lower-dimensional fibers. The proof of Lemma 39.2 uses only the signs of a finite bivariate polynomial family and the listed projections; it applies verbatim to this family. Its primitive factors are squarefree over $\mathbb R(s)$, distinct factors are coprime there, leading coefficients are included, and the two boundary factors are retained. All hypotheses explicitly checked in §39 therefore hold. Zero members keep sign zero. This supplies a fixed passing complete label on a continuous interior root section or sector midpoint for all sufficiently small positive $s$.

For that label, (45.7) has nonzero denominators throughout the cell and reconstructs one whole world at each scale. A nonzero gain numerator is required at every positive scale. It may tend to zero at the endpoint, as may the entire auxiliary gain vector. Since $P_{12}=1/s$ in chart $12$ and $P_{21}=1/s$ in chart $21$, a passing cell gives the claimed actual escape.

Conversely any original source-escaping sequence has a subsequence escaping in an off-diagonal coordinate, since both diagonal entries lie in $(0,1)$. Its exact chart parameters from Lemma 37.2 have $s\downarrow0$ and $0<x<s$. Theorem 45.2 gives a passing complete label at each such point, and the sequence equivalence in Lemma 39.2 makes the corresponding test pass. This proves both directional equivalences; Theorem 40.1 then gives (46.6), independently of the two families' choices of scale. If a failed test had a compatible source with its selected entry greater than $1/\varepsilon$, its own chart would have a passing point with $0<s<\varepsilon$, contradicting the same sign-cell equivalence. This proves the negative bounds. Finally (26.9) applies to every original whole world with these same raw prefix errors, giving the two coefficient bounds in (46.7) without any gain floor. $\square$

The positive-scale test never evaluates compatibility solely at $(\alpha,\beta)=(0,0)$. Thus $\delta=0$, arbitrary exact-radius contacts, either gain sign, degree drops and sampled gain roots remain exact. So do $\alpha/s$ or $\beta/s$ tending to an endpoint at arbitrary rates, and gains or auxiliary gains tending to zero. No asymptotic rate restriction is used in the necessity argument or in the root-section and sector coverage. Original source worlds are retained, rather than replaced by separate limiting coefficient approximants.

## 47. A common-error consumer and the existing opposite contacts

**Proposition 47.1 (marginally widened contrasts accept an impossible source).** Use exactly the five original-clock reads (29.1), with $k=d=0$. The record

$$
 y=(1,5/4,9/4,11/4,11/4),\qquad\delta=1/4
 \tag{47.1}
$$

has a legal noiseless producing world. Nevertheless the candidate source

$$
 P^{\rm c}=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
 \tag{47.2}
$$

has no compatible whole constant gain and drift, even though every adjacent first-difference contrast passes its independently widened error interval at the same nonzero candidate gain $h=1/2$.

**Proof.** The legal producing world is

$$
 P^{\rm a}=\begin{pmatrix}3/4&1/4\\3/4&1/4\end{pmatrix},
              \qquad H=1,\qquad D=0,\qquad\xi=0.
 \tag{47.3}
$$

Its source is strictly positive, trace one and rank one. Formula (29.5) gives precisely (47.1). The candidate source (47.2) has trace vector

$$
 a=(1,3/2,5/2,5/2,7/2).
 \tag{47.4}
$$

At $h=1/2$ the four residual first differences are

$$
 (y_{i+1}-y_i)-\tfrac12(a_{i+1}-a_i)
                  =(0,1/2,1/2,-1/2),\qquad 0\le i<4.
 \tag{47.5}
$$

Every one lies in the individually valid interval $[-2\delta,2\delta]=[-1/2,1/2]$; the drift cancels from these contrasts. But these four bounds are not a sufficient description of the image of the five-dimensional raw box. At this candidate gain, for example, the middle two contrasts would require $\xi_3-\xi_1=1$, whereas $|\xi_i|\le1/4$ permits magnitude at most $1/2$.

There is also an obstruction independent of the candidate gain value. The vector with coefficients $(1,-2,1)$ at clocks $(1,3,4)$ annihilates both the constant drift and the candidate trace vector (47.4). Hence every possible whole $h,D$ at this source would require

$$
 |y_1-2y_3+y_4|
       =|\xi_1-2\xi_3+\xi_4|
       \le(1+2+1)\delta=1.
 \tag{47.6}
$$

The left side is $3/2$, a contradiction. Thus this candidate source is impossible even though the original compatibility set is nonempty and the independent contrast intervals accept it. This is the elementary dual-norm lower bound for norm approximation, credited to Boyd–Vandenberghe, Example 5.6, specialized to these actual trace columns. Theorems 44.2 and 45.2 instead test membership in the full joint image $Z_\delta$ and reject this source. $\square$

**Corollary 47.2 (opposite exact contacts and delayed violations are preserved).** The new tests have the following values on the already proved five-read consumers:

$$
 \begin{array}{c|c|c}
 \text{received record and radius}&
        \widehat{\mathsf{Pass}}_{12}&\widehat{\mathsf{Pass}}_{21}\\ \hline
 y^{\rm B}=(0,2,0,0,0),\quad\delta=1
       &\mathrm{false}&\mathrm{false}\\
 y^{\rm U}=(1,7/10,17/10,19/10,21/10),\quad\delta=3/5
       &\mathrm{true}&\mathrm{false}\\
 y^{\rm E}=(0,5/2,3/2,1/2,3/2),\quad\delta=1
       &\mathrm{false}&\mathrm{false}
 \end{array}
 \tag{47.7}
$$

For $y^{\rm B}$ every positive inflation instead has at least one passing direction. In the family of Proposition 42.1, for every prescribed finite weak Taylor depth, the worlds at radius one still fail an exact raw constraint, despite their nonnegative truncated slacks and nonzero auxiliary contact gain.

**Proof.** Equation (46.6) transfers (40.2)–(40.3) directly. Proposition 34.1 supplies the inflation assertion, Proposition 41.1 the bounded nonzero-auxiliary contact, and Proposition 42.1 the exact positive violation (42.1) beyond any chosen finite depth. These are consumers of those existing results, without new proofs of their constructions. Theorem 45.2 excludes a complete passing reconstruction for a world violating an original raw inequality; Theorem 46.3 also excludes every escaping compatible family at radius one for $y^{\rm E}$. No finite-jet sign shortcut replaces the positive-scale signs in (46.5). $\square$

## 48. Credited inputs and the scope of the polynomial count

The standard interpolation input is Berrut and Trefethen, [*Barycentric Lagrange Interpolation*, SIAM Review 46(3), 501–517, DOI 10.1137/S0036144502417715, equations (2.1) and (3.2)](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf): Lagrange interpolation and its weights. The coefficient identity (44.12) and fixed-node drift reconstruction use those formulas directly. The weighted moment columns and their sign changes are elementary consequences used inside the same-world and counting arguments; interpolation is not claimed as new content.

The standard convex and polyhedral inputs are Boyd and Vandenberghe, [*Convex Optimization*, Example 5.6, printed pp. 254–255, equations (5.63)–(5.64), and §6.1.1, printed pp. 291–293](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), for norm-approximation duality and the Chebyshev LP; and Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorems 2, 4, 8, 13 and 15](https://arxiv.org/pdf/1001.2161v1), for Cramer's rule, the classical small-support convex representation, polyhedral structure, active-row vertices and the bounded convex-hull description. The facet and support-function arguments, and the affine-dependence elimination, are standard intermediate tools. They are not presented as discoveries or as a replacement for the explicit source-specific counts and reconstruction.

The project inputs are the exact paid-history source charts and injective compact fibers of §§37–38, the fully specified real-algebraic sign construction and its credited suppliers in §§39 and 43, the two-direction escape theorem and unchanged prefix coefficient bounds in §40 and (26.9), and the consumers in §§34–35 and 41–42. Their parameter correspondence is $P=X_\nu/(\alpha+\beta)$, $H=(\alpha+\beta)Q$, $D$ in the original clock variable, $s=\alpha+\beta$, and $x=\alpha$. All errors remain the original $\xi_i$ at all $L$ paid clocks. In particular the projection in (44.2) is postprocessing of those records, not a sensor or an acquisition root oracle.

The additional mathematical synthesis is repo-derived: the exact weighted drift quotient of this whole-world acquired fiber; its explicit joint-error facet and sign-change vertex lists with $r=3k+4$; elimination of only $p=k+1$ gain coefficients; complete determinant certificates including all raw-witness simplex labels; source-degree bounds independent of $d$; polynomial-in-$d$ label, projection and sample counts; and transfer to both original exact-radius escape directions and finite negative bounds. The common-error counterexample (47.1)–(47.6) supplies an explicit consumer of the joint rather than marginal error geometry. A bounded search not finding this combined statement is not evidence of literature priority, and the mature intermediate ingredients remain credited as above.

These are real-arithmetic mathematical statements for arbitrary received reals and nonnegative radius. Their certificate counts do not assert efficient enumeration, stable numerical evaluation, finite-bit computability for arbitrary real presentations, physical realization, literature novelty, optimal counts or Lean/kernel verification. No source bound, gain floor, gain normalization, sign choice, root exclusion or discarded paid read is introduced. Every successful reconstruction contains one actual legal $P,H,D$ and all original raw errors. Exact-radius boundedness and boundedness after positive radius inflation retain their different meanings.

## 追加锚（本行以下为增补区）

## 49. Rational records, paid-clock heights, and the size of the joint certificates

**Definition 49.1 (finite input and common algebraic output).** Fix $k,d\ge0$, $p=k+1$, $r=3k+4$, and exactly the history (26.2), with $L=3k+d+5$. A world and its errors have exactly the real domains in Definitions 25.1 and 30.1. Only the received $y_0,\ldots,y_{L-1}$ and the radius $\delta\ge0$ are now required to be rational. For a reduced rational $a/b$, $b>0$, charge

$$
 \ell(a/b)=1+\lceil\log_2(1+|a|)\rceil
                 +\lceil\log_2(1+b)\rceil.
 \tag{49.1}
$$

The integer degrees are binary encoded, the record is the ordered list at all $L$ original clocks, and put

$$
 \tau=2+\ell(k)+\ell(d)+\ell(\delta)
                         +\sum_{i=0}^{L-1}\ell(y_i).
 \tag{49.2}
$$

Here an integer in $\ell$ has denominator one. Parsing and checking the declared length and the sign of $\delta$ are charged. No real source coefficient is part of the input. A positive rational threshold $B$ has additional length $b=\ell(B)$; put $b=0$ when no threshold is requested.

A common real-algebraic representation of a whole world means a squarefree $F\in\mathbb Z[T]$, a rational open interval isolating one real root $\theta$ of $F$ (a specified rational root may instead be given as a rational point), a positive integer $a$, and integer polynomials $G_j$ of degree less than $\deg F$. Every output scalar is $G_j(\theta)/a$, using this same $\theta,a$. The scalar list consists of the four entries of $P$, all $p$ coefficients of the one whole $H$, all $d+1$ coefficients of the one whole $D$, and the $L$ original errors. Leading zero coefficients are retained. The algebraic degree of this representation is $\deg F$, not the number of output coordinates. It is not required that $F$ be irreducible. Purely rational worlds may be encoded using a degree-one $F$. Output length charges every integer coefficient, interval endpoint and list entry. All costs below are deterministic Turing bit operations; integer multiplication may be schoolbook multiplication.

**Theorem 49.2 (source-specific height control before real-root computation).** Use all complete certificates of §§44–46, with their original rational coefficients, and substitute $\alpha=x$, $\beta=s-x$. Retain identically zero polynomials as fixed zero signs. Write $\mathcal N$ for (46.3), and set

$$
 \begin{aligned}
 D_0&=2p,& a_0&=p+r+10,\\
 h&=2^{16a_0^2}
       \bigl(\tau+L^2\lceil\log_2(2L)\rceil+2\bigr).
 \end{aligned}
 \tag{49.3}
$$

The family of at most $\mathcal N$ source polynomials, including $x,s-x$, can be written as integer polynomials of total degree at most $D_0$ and coefficient bit length at most $h$, each obtained by multiplying its original rational polynomial by a known positive rational. All constant signs $c_T$ can also be computed exactly with numerator and denominator lengths at most $h$. Generation of these data, their labels and their raw sign vectors is possible in

$$
 O\!\left(2^{16a_0^2}(L+\mathcal N+1)^6(h+1)^2\right)
 \tag{49.4}
$$

bit operations. For a selected complete label the reconstruction in (45.7), including all coefficients of $D$, has rational-function descriptions whose numerator and denominator coefficient lengths are at most $h$ and whose source degrees are bounded by $D_0+2$. These descriptions can be generated within (49.4). They describe one common error lift, not independent error allowances for the moment coordinates.

**Proof.** The degree and label counts, and the exact equivalence of these certificates with the original fiber, are Theorems 45.2 and 46.1; they are used without new elimination of the original worlds. The height estimates and bit costs below are repo-derived for this paid history and its joint raw-error lift. Interpolation, determinant identities and the real-algebraic algorithms cited in the proofs remain their mature suppliers.

Let $q_y$ be the product of the positive input denominators of $\delta,y_0,\ldots,y_{L-1}$, and let

$$
             m_0=(L-1)!,\qquad R_0=m_0q_y.
 \tag{49.5}
$$

Then $\log_2 q_y\le\tau$ and $\log_2 m_0\le L\log_2 L$. All entries of $W$ have denominator dividing $m_0$, because

$$
 m_0\omega_i=(-1)^{L-1-i}\binom{L-1}{i}.
 \tag{49.6}
$$

Their numerator lengths are at most $L+r\lceil\log_2(2L)\rceil+2$. Every cumulative matrix $A_i$ is an integer matrix with entries of absolute value at most $2^i$: multiplication by either original atom $M,J$ increases the maximum row sum by at most a factor two. Constructing the entire consecutive history by $L-1$ such multiplications uses $O(L^3)$ bit operations, including storage. Powers of the clocks up to $d+r+p$ have at most $(d+r+p)\lceil\log_2(2L)\rceil+1$ bits and can be generated by repeated integer multiplication. In particular growing clock indices and Fibonacci matrix entries are not unit-cost constants.

The coefficients of $\rho_J$ have absolute value at most $(L+1)^{r-1}$. Combining this bound with (49.6), each sum defining $C_\nu,b,h_J,v_t,A_{\nu,\ell},\lambda_\ell$ has denominator dividing $R_0$ and numerator length bounded by

$$
 t_0=16a_0\bigl(\tau+L\lceil\log_2(2L)\rceil
                         +a_0\lceil\log_2(2a_0)\rceil+2\bigr).
 \tag{49.7}
$$

This includes the absolute values in $h_J$: they are signs of known rational integers at the original clocks. No algebraic sign service is needed for them. Computing the $F$ facet rows and $V$ vertices takes at most $O((F+V)L(r+p+1)^2)$ rational additions and multiplications of these bounded descriptions, in addition to generating the clock powers. The lists are exactly (44.7) and (44.10), rather than all $2^L$ box corners.

A determinant with $n$ columns, polynomial entries of degree at most two and entry numerator length $t_0$, has common denominator $R_0^n$. Expansion into its $n!$ products bounds every numerator coefficient length by

$$
 n t_0+\lceil\log_2(n!)\rceil
                     +n\lceil\log_2 6\rceil+2.
 \tag{49.8}
$$

The relevant orders are at most $p+1$ for reduced bases and slacks and $r+1$ for the error simplex. In $M_a$ the replaced column has denominator dividing $R_0^{p+1}$ and the other $r$ columns have denominators dividing $R_0$. Thus a common denominator $R_0^{a_0}$ clears every certificate polynomial and every $c_T$. All these powers are positive. Products by $\alpha+\beta$ and the substitution $\beta=s-x$ add at most $D_0+2$ bits per monomial expansion, up to the monomial-count logarithm. Equations (49.7)–(49.8), applied also to $u=\Delta b-CN$, are smaller than (49.3).

For the drift, interpolation of the $d+1$ residual values at $0,\ldots,d$ uses

$$
 D(\tau')=\sum_{i=0}^d R_i
       \frac{\prod_{0\le j\le d,\,j\ne i}(\tau'-j)}
                    {(-1)^{d-i}i!(d-i)!}.
 \tag{49.9}
$$

The denominators divide $d!$, and numerator coefficients have length $O(d\log(2d))$. Applying this linear expression to the common rational-function residuals (46.4) adds only $O(L^2\log(2L))$ to a coefficient-length bound. The common source denominator is $\alpha+\beta$; the other nonconstant denominators are $\Delta$ and $c_T\Delta$. The degree estimates in §46 and these expressions give the asserted conservative $D_0+2$ bound. The constant factorial denominators are charged in $h$. Formula (49.9) is the same fixed-node Lagrange input already credited to Berrut–Trefethen in §48; it is not a new interpolation theorem.

For cost, generate subsets in their specified order and evaluate the displayed determinant expansions with exact integers and known denominators. Their largest order is bounded by $a_0$. The number of reduced bases, complete labels and constant simplices is bounded by the quantities in (46.1)–(46.3); the additional loops over raw clocks, monomials and output coefficients have at most a fixed power of $L+\mathcal N+1$. The factors $a_0!$, the bounded-degree polynomial multiplications and all their monomial counts are less than $2^{16a_0^2}$. Schoolbook integer operations on the lengths just bounded, with sequential summation using common denominators, give (49.4). This also accounts for enumerating the labels that are subsequently rejected as singular. The calculation uses integer/rational arithmetic only. $\square$

## 50. Exact finite-bit decisions with exceptional fibers included

**Definition 50.1 (quantitative parameters for the same received record).** For the integer source family of Theorem 49.2 put

$$
 \begin{aligned}
 E&=8(D_0+1)^2,& A&=E^2D_0,\\
 J&=(2D_0+2)^8(h+1),&
 M_0&=10(\mathcal N+1)^2(D_0+1)^4,\\
 K_0&=(2A+2)^{100(A+1)^2},&
 \eta&=2^{-(J+3)},\qquad U=2^{J+3}.
 \end{aligned}
 \tag{50.1}
$$

These deliberately coarse integer parameters are computable from the finite input. $J$ is a coefficient-length bound, not an uncharged precision oracle. Writing the dyadic $\eta$ or the integer $U$ in ordinary binary charges $J+O(1)$ bits.

**Theorem 50.2 (full real-world semantics and polynomial bit decision).** There is a deterministic finite-bit algorithm for every $k,d\ge0$ and every input of Definition 49.1 which returns separately:

1. whether $\mathcal W_\delta(y)$ is nonempty;
2. for each $\nu\in\{12,21\}$, whether its original source entry is unbounded on $\mathcal W_\delta(y)$;
3. for each failed direction, the valid finite bound $P_\nu\le U$ for every original compatible real world. If the class is empty, it instead reports emptiness and may return the vacuous bound zero.

Here $P_\nu$ denotes $P_{12}$ or $P_{21}$, as appropriate. A nonempty compatibility answer can also return one whole world in the common representation of Definition 49.1, with degree at most $A$. The algorithm, including that optional world, costs at most

$$
 O\!\left(K_0(L+\mathcal N+1)^{12}(h+1)^{12}\right).
 \tag{50.2}
$$

The constants in $O$ are absolute. All roots, zeros, signs, projections and reconstructions are included. In particular this is a polynomial bit bound in $d$ and actual input length for every fixed $k$, rather than a polynomial certificate count or an invocation of an uncosted real decision procedure.

**Proof.** Use the following mature projection input inside the source-specific decision. Apply Basu–Pollack–Roy, [*Algorithms in Real Algebraic Geometry*, second edition, Theorem 5.16 and Algorithm 11.1, printed pp. 165–166 and 403–405](https://www.maths.ed.ac.uk/~v1ranick/papers/basupollackroy.pdf), eliminating only $x$ from the integer family in $(s,x)$. Their ordered integral domain is $\mathbb Z$, contained in the real closed field $\mathbb R$. Their truncations, leading coefficients and signed principal subresultant coefficients are all retained. Adjoin $s$ and all nonzero coefficient polynomials in $s$ of the input family. Constants may be retained; identically zero projection polynomials are removed by integer coefficient inspection.

For specificity, the truncations are every initial segment $\sum_{j=0}^t f_j(s)x^j$ of each $f$. The projection uses their leading coefficients, their signed principal subresultant coefficients with their own $x$ derivatives, and those of each pair of truncations. The equal-degree pair is first reduced by the leading-coefficient combination specified in Algorithm 11.1. Thus degree drops are covered before specializing $s$; a single discriminant is not substituted for this projection. This is a direct use of the supplier, not a new projection algorithm.

The enlarged projection has at most $M_0$ members, degree at most $E$, and integer coefficient length at most $J$. Indeed there are at most $\mathcal N(D_0+1)$ truncations and $O(\mathcal N^2(D_0+1)^3)$ principal coefficients. Each is a determinant of order at most $2D_0$ with entries consisting of original coefficients, their derivative multiples, or the leading-coefficient combination of two original polynomials. Those entries have $s$ degree at most $2D_0$ and length at most $2h+O(\log(D_0+1))$. Expanding each determinant bounds its degree by $4D_0^2$ and its coefficient length by $O(D_0(h+D_0\log(D_0+1)))$. The larger explicit $E,J,M_0$ in (50.1) dominate these bounds. They also dominate the added coefficients and $s$. Generation by determinant expansion has bit cost bounded by a fixed polynomial in $\mathcal N,h+1$ times $(2D_0+2)^{O(D_0)}$, which is absorbed by (50.2). No factorization over $\mathbb R$, $\mathbb R(s)$ or $\mathbb Q(s)$ is required.

The supplier's conclusion is used as follows. Over each open interval of $s$ on which no nonzero projection member vanishes, all real roots of all nonzero specialized input polynomials have continuous ordered sections, with fixed incidences and multiplicities. Every original polynomial has constant sign on each section and each intervening band. A polynomial identically zero on such a cylinder keeps sign zero. The two boundary polynomials $x,s-x$ are in the input family, so these statements also hold after restricting to $0<x<s$. They include repeated roots and shared factors. At a projection root the algorithm below samples the specialized fiber itself; no assertion of generic degree or non-nullification is made there.

Here are the finite-bit sampling details, including the exceptional algebraic fibers. The univariate integer operations used are Basu–Pollack–Roy Algorithms 10.4 and 10.6–10.8, printed pp. 372–382: squarefree real-root isolation, signs at roots, comparison and univariate sample points. On $n$ polynomials of degree at most $q$ and coefficient length at most $t$, their bound is $O(n^2q^5(t+\log(q+1))^2)$, using maxima over every polynomial whose sign or root is tested. They return actual real algebraic roots and rational sector samples. No infinitesimal specialization is used. The following reduction to those integer routines supplies the binary lifting estimate that is not asserted by the general lifting discussion in the supplier's §11.1.2.

First isolate and order the roots of all projection members using these integer routines. Sample every positive projection root and every open subinterval of $(0,\infty)$ cut out by those roots, including the final unbounded interval. Open-interval samples can be rational dyadics, chosen from the isolating intervals; the outer root bound supplies the final one. There are at most $2M_0E+1$ such base samples. A base sample $s_0$ is either rational, or is represented by a squarefree $u\in\mathbb Z[S]$ of degree $e\le E$ and an isolating rational interval. For a rational sample use a linear $u$. Its coefficient and interval lengths are bounded by $(2E+2)^{10}(J+1)$; this follows either from the isolation bounds just quoted or from the elementary root-separation estimate below.

At this selected $s_0$, test every coefficient of every $f(S,X)$ for zero by the integer univariate sign routine at $s_0$. A specialized polynomial all of whose coefficients vanish is recorded as the zero polynomial. For any other $f$, form

$$
 \begin{aligned}
 g_f&=\gcd\bigl(u,f_0,\ldots,f_{D_0}\bigr),
       &u_f&=u/g_f,\\
 R_f(X)&=\operatorname{Res}_S(u_f(S),f(S,X)).
 \end{aligned}
 \tag{50.3}
$$

Zero coefficients may be omitted from the gcd, and rational denominators are cleared positively. The chosen $s_0$ remains a root of $u_f$, since $f(s_0,X)$ was not zero. Moreover $R_f$ is a nonzero integer polynomial: $u_f$ is squarefree and no one of its complex roots annihilates every coefficient of $f$. Equivalently the product of the nonzero conjugate specialized polynomials, times its known leading factor, is not zero. Its degree is at most $eD_0$ and it vanishes at every actual root of $f(s_0,X)$. The resultant determinant has order at most $E+D_0$, so its coefficient lengths are bounded by a power of $2E+2$ times $h+J+1$. Gcd and resultant computations here use only integer polynomial arithmetic; signed subresultants or determinant expansions give these bounds directly.

Isolate the roots of all the nonzero $R_f$, merge these lists exactly, and take their real roots and rational points between consecutive roots, also including the two outer intervals. These are a superset of all necessary fiber samples. Extraneous roots arising from other conjugates of $s_0$ merely subdivide an actual sector. They cannot omit a root or change a sign between actual roots. There are at most $2\mathcal N ED_0+1$ fiber samples. Include all roots, even multiple or exactly active ones, after squarefree isolation; no strict inequality is substituted for an equality. To finish, evaluate all original $f(s_0,x_0)$ signs at each candidate, discard those failing $0<x_0<s_0$, and evaluate the complete predicates.

For completeness, those bivariate sign evaluations have the following bounded integer construction. Let $u$ and $v$ be the squarefree integer polynomials isolating $s_0,x_0$, of degrees $e\le E$ and $m\le ED_0$. Put $n=em\le A$. In the rational algebra

$$
             \mathcal A=\mathbb Q[S,X]/(u(S),v(X))
 \tag{50.4}
$$

use the $n$ monomials $S^iX^j$, $i<e,j<m$. This is a product of $n$ distinct complex points after extending scalars. Among the integers

$$
                   1\le c\le\binom n2+1
 \tag{50.5}
$$

one makes $T=S+cX$ have distinct values at all these points. Each pair of distinct points rules out at most one $c$, since equality with identical $X$ and different $S$ rules out none. Compute the multiplication matrix of $S+cX$ and its characteristic polynomial, clearing a positive rational denominator to obtain $F_c\in\mathbb Z[T]$. Its squarefreeness, decided by $\gcd(F_c,F_c')=1$, is precisely the separating condition. Thus the finite enumeration (50.5) finds a separating $c$ without a primitive-element oracle. The powers $1,T,\ldots,T^{n-1}$ then form a basis: after extending scalars their value matrix is an invertible Vandermonde matrix. Rational linear systems therefore express $S,X$ as polynomials in $T$ of degree less than $n$. All these matrices have rational entries, and common denominators and determinant bounds control their sizes. This is the standard separating-element form of a rational univariate representation, as in Basu–Pollack–Roy §12.4 and Proposition 12.16, used here only on the explicitly bounded product algebra (50.4).

The root $\theta=s_0+cx_0$ is selected by refining the two given isolating intervals and isolating $F_c$. Reduction of $f(S,X)$ using the two coordinate polynomials gives a rational polynomial in $\theta$. Clear its rational denominator positively and use Algorithm 10.6 to obtain its exact sign, including zero. This also provides a common representation of $s_0,x_0$, of degree at most $A$. It is harmless that (50.4) may contain other embeddings: the selected real root and its recovered two coordinates specify precisely the chosen pair.

Here are explicit height and termination controls for the refinements and linear algebra. A squarefree integer polynomial of degree $q$ and coefficient length $t$ has roots of modulus at most $2^{t+1}$ and distinct roots at distance greater than

$$
                         2^{-2q^2(t+2)}.
 \tag{50.6}
$$

For the first bound use the usual geometric-series root bound. For the second use its nonzero integer discriminant: the leading-coefficient power is at most $2^{(2q-2)t}$, every root difference other than a chosen closest pair is at most $2^{t+2}$, and the discriminant's absolute value is at least one. These inequalities imply (50.6), with room in the exponent. To compare roots of two polynomials use the squarefree part of their product; gcd first distinguishes equality. Factor coefficient heights for this squarefree part are bounded by the original height plus $O(q+\log(q+1))$, by the ordinary integer factor bound, also given in Basu–Pollack–Roy Corollary 10.12. Thus separation requires only polynomially many bits in these degrees and heights, not a numerical positive-gap promise.

In (50.3) the degrees are at most $ED_0$. In (50.4) the dimension is at most $A$; at most $\binom A2+1$ separating integers are tried. Reduction of monomials, characteristic determinants, and Cramer's rule for the coordinate basis have orders and degrees bounded by powers of $A+1$. Expanding them bounds every coefficient length by $(2A+2)^{20(A+1)}$ times the input height at this step. The isolating refinements needed to identify $s_0+cx_0$ are bounded by (50.6) for $F_c$, together with $O(\log(A+1))$ bits for $c$. Exact zero is settled by gcd/sign computation before refinement for a nonzero sign. Consequently all operations on one such pair, including every sign of the input family, have bit cost bounded by

$$
 O\!\left((2A+2)^{60(A+1)^2}
           (\mathcal N+1)^2(h+J+1)^6\right).
 \tag{50.7}
$$

This estimate follows just by the determinant expansions, schoolbook rational arithmetic and the quoted integer isolation bounds; no unit-cost operation in an algebraic coefficient field is hidden in it. Denominator clearing in the $A$-dimensional matrices and all coefficient products are included. Rational sector samples use a linear $v$ and satisfy the same estimate. The number of base samples is $O(M_0E)$, the number of fiber samples per base is $O(\mathcal N ED_0)$, and scanning the complete labels and their signed constraints costs at most a further $O((L+\mathcal N+1)^2)$ per sample. Substitution of $M_0,J$ and enlargement to $K_0$ give (50.2), including Theorem 49.2. These bounds are intentionally larger than the individual arithmetic costs.

A passing sample for either chart is now equivalent to nonempty compatibility. Sufficiency is the whole-world reconstruction in Theorem 45.2. For necessity take any original compatible real world, use its own chart parameters and its original whole gain, drift and all errors in (44.4), and then Theorem 45.2. The corresponding source point lies over either a projection root or an open base interval. In the former case its specialized fiber was sampled, including nullified polynomials; in the latter the credited sign-invariant sections and bands transfer its complete sign predicate to the chosen base sample. Thus some sampled predicate passes. This proves the separate nonemptiness answer, even for isolated sources, lower-dimensional coefficient fibers and zero radius. The algorithm need not enumerate the continuum of possible original worlds to retain this equivalence.

It remains to decide unboundedness and prove the numerical bound. For each nonzero projection polynomial divide out its power of $s$ conceptually. Its nonzero constant coefficient has absolute value at least one and its coefficients have absolute value at most $2^J$. Applying the root bound to its reversed polynomial gives, for every nonzero root $z$,

$$
                  |z|\ge\frac1{1+2^J}>2^{-(J+1)}.
 \tag{50.8}
$$

Thus the whole interval $(0,\eta)$ contains no positive projection root, regardless of how many projection members vanish at zero. Sample the single rational scale $s_*=\eta/2$ and its fibers by the same finite-bit procedure. Define a directional pass by the existence of a passing complete label in that fiber. The sign-invariant sections and bands, with the boundary sections $x=0,s$, show that such a label exists at every scale $0<s<\eta$ if it exists at one; if there is none at $s_*$ there is none throughout this interval. This is the same positive-scale implication proved in Lemma 39.2, now using the supplier's truncation/subresultant projection rather than the real factorization in (39.2).

A directional pass gives compatible original worlds at every such positive scale, with the selected source entry exactly $1/s$, by (37.1) and Theorem 45.2. Conversely, if that original entry is unbounded, its own chart has a sequence $s=1/P_\nu\downarrow0$. Its complete predicates must pass at those points, so sign invariance forces the directional test to pass. If the test fails, any compatible real world with $P_\nu>U=1/\eta$ would have $0<s<\eta$ and a passing predicate, a contradiction. The weak bound $P_\nu\le U$ includes equality. Empty classes are distinguished by the preceding independent feasibility answer. Reconstruction and the common-output height estimate are completed in Theorem 51.1; they use only a selected passing sample and are included in the cost already allowed in (50.2). $\square$

## 51. Whole algebraic worlds beyond every rational threshold

**Theorem 51.1 (threshold witnesses and output length).** For the same finite input, suppose the directional test of Theorem 50.2 passes. For every rational $B>0$ there is a deterministic construction returning one actual world and all original errors in the common representation of Definition 49.1, such that

$$
 \begin{gathered}
 P_{ab}>0,\quad \det P=0,\quad\operatorname{tr}P=1,
 \qquad 0\ne H\in\Pi_k,\quad D\in\Pi_d,\\
 y_i=H(i)\operatorname{tr}(A_iP)+D(i)+\xi_i,
       \qquad |\xi_i|\le\delta\quad(0\le i<L),
       \qquad P_\nu>B.
 \end{gathered}
 \tag{51.1}
$$

For either a nonemptiness witness or a threshold witness, the representation degree is at most $A$ of (50.1). The lengths of each integer coefficient and each isolating endpoint, including a common output denominator, are at most

$$
                K_0(L+1)^4(h+b+1)^4.
 \tag{51.2}
$$

The number of output scalars is $4+p+(d+1)+L$, each with fewer than $A$ coefficient slots. Complete decision and threshold construction, including writing the output, cost at most

$$
 O\!\left(K_0(L+\mathcal N+1)^{12}(h+b+1)^{12}\right).
 \tag{51.3}
$$

In particular, writing $e_0=(r-1)(p+r+1)=12k^2+30k+18$, this is also bounded by

$$
       O_k\!\left((d+\tau+b+2)^{12e_0+36}\right).
 \tag{51.4}
$$

No bound on the actual real source or nuisance coefficients is supplied to the construction.

**Proof.** Choose the rational dyadic scale

$$
                s_B=2^{-(J+4+b)}.
 \tag{51.5}
$$

It belongs to $(0,\eta)$, and $1/s_B>B$, since $B<2^b$. The passing-direction equivalence in Theorem 50.2 guarantees a complete passing label at this scale. Compute fiber samples and signs there, and select any such label $(\nu,I,T)$. At the selected $0<x_B<s_B$, set $\alpha=x_B$, $\beta=s_B-x_B$ and use exactly (45.7). No limit world or coefficientwise approximant is used: $P$, the whole $H=(\alpha+\beta)Q$, the whole interpolated $D$, and all errors come from the one selected pair and label.

In detail, $\Delta\ne0$, $c_T\ne0$, and some $N_j\ne0$. The $q_j=N_j/\Delta$ give a nonzero whole polynomial $Q$. The weights $\mu_a=M_a/(c_T\Delta)$ are nonnegative and sum to $\delta$; hence the same errors $\xi_i=\sum_a\mu_a\sigma_i^{t_a}$ have $|\xi_i|\le\delta$ and satisfy $W\xi=b-Cq$. Formula (49.9) therefore gives the unique $D$ agreeing with all $L$ residuals, by (44.13). The source chart gives strict entrywise positivity, rank one, trace one, and $P_\nu=1/s_B$. These are precisely the reconstruction facts of Theorem 45.2, used on the same original clocks and box. When $\delta=0$ the nonnegative weights all vanish, and every original error is zero. There is no division by $\delta$ or by an unknown sampled gain.

At this rational scale each specialized integer polynomial has degree at most $D_0$ in $x$ and coefficient length at most

$$
                   h+D_0(J+4+b)+O(\log(D_0+1)).
 \tag{51.6}
$$

The integer isolation and sign routines therefore produce actual algebraic $x_B$, or a rational sector sample, with polynomially bounded coefficient and isolation lengths. The common field for a threshold witness can in fact be obtained using just this one algebraic $x_B$ and the rational $s_B$. For a general feasibility witness, use the common $\theta$ of degree at most $A$ constructed from its selected base and fiber sample in (50.4)–(50.5). Both cases satisfy the same bound $A$, without assuming a stronger primitive degree assertion for arbitrary fibers.

Here is the remaining common-denominator step, including the possibility that the representation polynomial has irrelevant conjugate factors. Express $s,x$ by the coordinate polynomials in $\theta$. Substitute these in the selected rational-function descriptions from Theorem 49.2 and reduce modulo the squarefree $F$ of the selected representation. All nonconstant divisors are products of $s,\Delta,c_T$, none of which vanishes at the selected root. Form one product $V(T)$ containing these divisors, and compute $G=\gcd(F,V)$. The selected root is not a root of $G$, as already decided by its exact signs. Replace $F$ by $F/G$, retain its isolating interval and reduce the coordinate polynomials again. Now $V$ is invertible modulo $F$ by the extended Euclidean algorithm. Thus every output scalar becomes a polynomial in $\theta$ with rational coefficients. This removes zero divisors at other embeddings without discarding the actual chosen world. Multiplying all positive rational coefficient denominators gives one positive integer $a$ and the integer $G_j$ of Definition 49.1.

The dimension never exceeds $A$. Resultant, coordinate-basis and inverse computations use matrices or polynomial Euclidean computations of order bounded by powers of $A+1$. Equations (49.8), (50.6) and (51.6) bound their intermediate and final coefficient lengths by a constant depending explicitly on $A$ times $h+J+b+1$. Formula (49.9) adds at most $O(L^2\log(2L))$ bits to each unreduced drift coefficient. There are $O(L+p+1)$ output scalars and at most $A$ rational coefficients per scalar. Taking the product of their denominators increases length by at most the sum of these lengths, rather than an exponential in their number. These estimates are smaller than (51.2), using $J=(2D_0+2)^8(h+1)$ and the deliberately larger $K_0$. The same bounds cover the isolating intervals after the gcd restriction.

For cost, compute only the selected world's $q,\mu,\xi$ and drift coefficients. Horner evaluation, polynomial reduction and common-denominator arithmetic in dimension at most $A$ have polynomial bit cost in the lengths just bounded. Fixed-node interpolation can be performed by the displayed $d+1$ Lagrange products, using a polynomial number of operations in $L$. Every one of the $L$ raw equations can also be evaluated in this representation with the same charged lengths; their validity here follows universally from the same-world reconstruction, rather than from a numerical tolerance. This reconstruction, its output storage and the extra fiber sampling at $s_B$ fit in (51.3). The nonemptiness witness in Theorem 50.2 uses the same reconstruction with $b=0$, so its asserted cost and degree are also established without circular dependence on the decision.

Finally Theorem 46.1 gives $\mathcal N=O_k(L^{e_0})$; this counts all lift numerators as well as the reduced predicates. Also $L\le(3k+5)(d+1)$ and (49.3) gives $h=O_k((d+\tau+b+2)^3)$. Substituting these inequalities in (51.3) proves (51.4). The bit bound is not an optimality statement.

All world quantifiers remain over the original real domains. The original-world-to-certificate implication in Theorem 45.2 starts with the world's own $P,H,D,\xi$; it does not rationalize its coefficients or change any one of its errors. The global feasibility test specializes exceptional fibers before sampling them and retains zero polynomials. The directional test instead works on the full interval $0<s<\eta$ and uses exact sections and sectors, including their zero signs. A sequence with any endpoint rate enters this interval and is covered by the same sign-invariant decomposition: neither $x/s$ nor its complement is bounded away from zero. The reconstructed actual gain is nonzero because $s>0$, $\Delta\ne0$ and some $N_j\ne0$ at the chosen point; its coefficients and its limiting auxiliary gain need not have a positive uniform lower bound along other scales. Thus empty and lower-dimensional fibers, exact contacts, gain roots, either gain sign and all degree drops remain included. These facts use the same whole world rather than separately chosen marginal fits. The conclusions concern exact mathematics under the stated model and radius; they assert no empirical validation of those premises, physical realization, literature priority or formal kernel verification. $\square$

## 52. A five-read height boundary for finite source bounds

**Proposition 52.1 (fixed certificate counts do not bound numerical source size).** Use the original five-read history (29.1), $k=d=0$, and the fixed rational record

$$
             y^{\rm U}=(1,7/10,17/10,19/10,21/10).
 \tag{52.1}
$$

For every rational $x\ge4$ put

$$
 \delta_x=\frac35-\frac1{10x},\qquad
 P_x=\begin{pmatrix}1/2&x\\1/(4x)&1/2\end{pmatrix},\qquad
 H_x=\frac9{10x},\qquad D_x=\frac25-\frac4{5x}.
 \tag{52.2}
$$

Then $\mathcal W_{\delta_x}(y^{\rm U})$ is nonempty and both escape directions fail. Nevertheless it contains this whole world with $P_{12}=x$. In particular, for $x=2^n$, $n\ge2$, the total rational input length is $O(n)$, both directional bounds are finite, and every valid $12$ bound is at least $2^n$. The label and projection count bounds depending only on $k,d$ are constant throughout this family. At the limiting rational radius $3/5$ the $12$ direction passes. Consequently a classifier receiving only a radius interval of prescribed positive width cannot always determine $12$ escape correctly, even when the exact record is supplied and every promised exact radius is rational with a nonempty compatibility class.

**Proof.** Strict source legality and nonzero constant gain follow directly from (52.2). This uses the source and gain in (35.3), but increases its single whole drift by $1/(10x)$. Thus its residual $z-y^{\rm U}$ at the five original clocks is exactly

$$
 \begin{aligned}
 r_0&=-\frac35+\frac1{10x}=-\delta_x,\\
 r_1&=\frac35-\frac7{20x}+\frac9{40x^2},\\
 r_2&=-\frac25+\frac{11}{20x}+\frac9{40x^2},\\
 r_3&=-\frac35+\frac1{10x}+\frac9{20x^2},\\
 r_4&=\frac1{10}+\frac1x+\frac9{40x^2}.
 \end{aligned}
 \tag{52.3}
$$

For $x\ge4$, $r_1>0$ and

$$
 \delta_x-r_1=\frac1{4x}-\frac9{40x^2}>0.
 \tag{52.4}
$$

For the middle coordinate,

$$
 r_2+\delta_x=\frac15+\frac9{20x}+\frac9{40x^2}>0,
 \qquad
 \delta_x-r_2=1-\frac{13}{20x}-\frac9{40x^2}>0.
 \tag{52.5}
$$

Also $r_3=-\delta_x+9/(20x^2)$, with $0<9/(20x^2)<2\delta_x$, and $r_4>0$ with

$$
             \delta_x-r_4=
                \frac12-\frac{11}{10x}-\frac9{40x^2}>0.
 \tag{52.6}
$$

The final strict inequality follows by evaluating the two decreasing positive subtracted terms at $x=4$. Taking all five original errors to be $\xi_i=-r_i$ proves compatibility, including exact contact at clock zero. The only change from the supplied family is the one common drift; no per-read gain or independently chosen residual is used.

The supplier Proposition 35.1 gives

$$
 \operatorname{dist}_\infty(y^{\rm U},\mathcal E_{12})=3/5,
 \qquad
 \operatorname{dist}_\infty(y^{\rm U},\mathcal E_{21})=7/10.
 \tag{52.7}
$$

Since $\delta_x<3/5$, the existing finite-record limit theorem, Theorem 30.2, excludes an unbounded source subsequence in either direction: such a subsequence would give a point of the corresponding $\mathcal E_\nu$ inside this very closed radius-$\delta_x$ box, contradicting (52.7). Thus both directions fail, while the displayed world forces every valid $12$ bound to be at least $x$. For $x=2^n$ the reduced numerator and denominator of $\delta_x=(6\cdot2^n-1)/(10\cdot2^n)$ have $O(n)$ bits, and the other input data are fixed. Any nonnegative rational upper bound at least $2^n$ has a numerator with at least $n+1$ binary bits. This proves the encoding and numerical-height assertion. At radius $3/5$ the original family (35.3) proves actual $12$ escape, as already used in (40.3).

For the interval assertion, given any $\epsilon>0$, choose $n\ge2$ with $1/(10\cdot2^n)<\epsilon$. Both $\delta_{2^n}$ and $3/5$ lie in the interval $[3/5-\epsilon,3/5]$. The preceding proof gives nonemptiness and a failed $12$ direction at the former rational input, and a passing $12$ direction at the latter. The same radius interval and exact received record therefore admit two different correct Boolean answers. A rule using only that interval must be wrong on one of them. Exact finite-bit rational input distinguishes them by their encoded denominators, and Theorems 50.2–51.1 charge this height and the necessary algebraic operations. This is an information obstruction for the interval-only replacement, not a lower bound on optimal Turing running time.

The new content of this consumer is the inward-radius whole-world family (52.2), together with its finite but necessarily growing directional bounds. Its inputs are the existing same-history contact example and limit-space exclusions, not a new general root-separation theorem. It shows why the height parameters and binary output lengths in §§49–51 carry mathematical information absent from a count of certificate labels. $\square$

## 追加锚（本行以下为增补区）

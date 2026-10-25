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

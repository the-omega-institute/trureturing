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

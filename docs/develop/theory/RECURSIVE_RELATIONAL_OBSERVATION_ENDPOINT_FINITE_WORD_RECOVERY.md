# Recursive relational observation: critical-radius finite-word recovery

> **Volume contract.** This `generic-v1` theory reference volume retains its published header and chapters byte for byte. Corrections and additions belong after the final append anchor.

**Source and proof status.** The content is repo-derived ordinary mathematical theory, with its reused sources and proof limits stated in §96.5. It is reference input; Lean declarations and proofs remain the mathematical truth source of the repository. This volume supplies no new Lean/kernel verification or physical validation.

**Supplier and numbering.** The complete [Parameterized Cross Product Recovery volume](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) is called the **supplier**. Its §§1–88 supply the original source, notation, published proofs, ten regimes, finite-word conventions and paid acquisition contracts. A reference labeled `supplier` points to that volume; §§89–96 and their numbered items are local to this continuation. The original section numbers are retained. Definitions, guards and interface/resource limits apply with the hypotheses of their cited statements; the supplier is linked in full rather than reproduced.

## 追加锚（本行以下为增补区）
## 89. The critical-radius complete-word law

The endpoint below concerns the actual source of [supplier §§1–5](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) and the complete numerical-word convention of [supplier §75](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). A source is a nonempty finite ordered tree with leaves $\alpha,\beta$ and interpretation $E_{a,b}(\langle s,t\rangle)=E_{a,b}(s)\times E_{a,b}(t)$ in oriented Euclidean $\mathbb R^3$. One preparation $(a,b)$ and one frame remain fixed throughout $x_j=E_{a,b}(\rho^jt)$, where $\rho\alpha=\beta$ and $\rho\beta=\langle\beta,\alpha\rangle$. The observation schedule is the original three Reads, two intervening destructive substitutions, and Stop. The required answers are numerical vectors for every finite $j\geq3$, with error measured by the unweighted supremum over the entire future.

**Definition 89.1 (domain and complete words).** Fix

$$
\varphi=\frac{1+\sqrt5}{2},\qquad L>1,\qquad
1<d_0<L^{2/\varphi^2},\qquad H=1.
$$

Retain every actual source satisfying $\|a\|,\|b\|\leq L$, $\Delta=\|a\|^2\|b\|^2-(a\cdot b)^2\geq d_0$ and $q_i=\|x_i\|\leq1$ for $i=0,1,2$, including zero-label histories. Let $C_N(E)$ be [supplier §75](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)'s minimum worst-case complete numerical binary-word length on the sources with at most $N$ original leaves. A word includes every source-dependent program, mode, precision, scale, coefficient, coordinate, constant and selection. One fixed finite interpreter receives only the complete word and a finite query; its actual description and installation costs are charged. Source-aware selection is permitted in this representation definition. It does not assert that the original observer can acquire the selected word.

The end of the complete word is already a framing boundary in [supplier Definition 76.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). Words need not be prefix-free. Constant transport start/end symbols, when used, have their actual constant cost. No independently supplied source-specific length, $N$, preparation, control hint or later name access is a decoder input. Here $N$ is only a proof stratum; the source domain remains unbounded. Mandatory evidence is treated in Definition 92.3, with no assumed bound on its length.

**Theorem 89.2 (sharp critical-radius numerical length).** There are constants $c_-,c_+$ and $N_0$, depending only on the fixed $L,d_0$ and the fixed interpreter/framing convention, such that

$$
\log_2\log_2N-c_-\leq C_N(1/2)
\leq\log_2\log_2N+c_+,\qquad N\geq N_0.
$$

Thus $C_N(1/2)=\log_2\log_2N+O_{L,d_0}(1)$, its ratio to $\log_2\log_2N$ tends to one, and the minimum number of radius-$1/2$ centers is $\Theta_{L,d_0}(\log N)$. The lower permits arbitrary real center trajectories, so it applies in particular to terminating finite-output decoders. The upper uses one fixed finite arithmetic interpreter independent of $N,L,d_0$. An additional prefix-free requirement has the separately paid sufficient representation in Definition 92.2. No optimal additive constant or optimal prefix-free overhead is asserted.

**Reused source identities 89.3.** The transport $E_p(\rho t)=E_{(b,b\times a)}(t)$, five-vector descriptor table, actual projection and signed closure are those of [supplier §§3–5,16,35,50,64.3,77](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). In particular, with $w=x_2\times x_1$,

$$
|x_0\cdot w|\geq q_2^2,\qquad q_2\leq q_0q_1,
\qquad x_3=\operatorname{sgn}(x_0\cdot w)w,
\qquad\operatorname{sgn}(0)=0.
$$

These assertions require an actual common-source history, not an arbitrary triple. The sign uses $x_0\cdot(x_2\times x_1)=-\det[x_0,x_1,x_2]$ in column determinant notation. For a nonzero unit label with actual counts $(m,n)$, $r=\|b\|$ and $s=\sqrt\Delta$,

$$
q_1=r^ms^n,\qquad q_2=r^ns^{m+n},\qquad
q_j=q_1^{F_{j-2}}q_2^{F_{j-1}}\quad(j\geq3),
$$

where $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$ and $0^0=1$. The phase directions have period three. A zero unit label has $x_j=0$ for $j\geq1$, even when $x_0\ne0$. The unconditional dependent-preparation branch has $x_j=0$ for $j\geq2$; $d_0>0$ excludes it from this domain.

The integer determinant theorem is already [supplier Theorem 67.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). With $z_0=\log\sqrt{d_0}>0$ and $Q=m^2+mn-n^2\ne0$, it gives

$$
-\log q_2\geq\frac{z_0|Q|}{\max(m,n)}
\geq\frac{z_0}{m+n}.
$$

Consequently, putting $U=q_1^2$, $V=q_2^2$, $D=(1-U)+(1-V)$ and $c_0=1-1/d_0>0$, the loss consequence in [supplier §77](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) is

$$
D\geq1-q_2^2\geq1-d_0^{-1/(m+n)}
\geq\frac{c_0}{m+n}\geq\frac{c_0}{N}.
$$

The penultimate step is the concavity chord for $1-\exp(-t\log d_0)$ on $0\leq t\leq1$. Zero labels have $D=2$ and satisfy the last bound directly. Thus every source in Definition 89.1 has $D>0$. This is reuse of the sharper published determinant bridge, not another determinant theorem or a leaf-count observation port.

## 90. An actual phase bank and its finite total directional area

**Lemma 90.1 (Family A, size, rate and signs).** Choose once

$$
\sqrt{d_0}<s<L^{1/\varphi^2},\qquad z=\log s>0.
$$

For sufficiently large positive $k\equiv0\pmod6$, set

$$
m=F_k,\quad n=F_{k+1},\quad t_k=\rho^{k+1}\alpha,
\quad N_k=F_{k+2}=m+n,\quad
p_k=(s^{1+n/m}e_1,s^{-n/m}e_2).
$$

These are actual jointly admissible sources with one fixed preparation per execution. Their first norms are $q_0=q_2=e^{-z/m}$ and $q_1=1$, and

$$
x_j=e^{-\lambda_kF_{j-1}}u_j\quad(j\geq3),\qquad
\lambda_k=z/F_k,
$$

where $u_j$ is $e_2,-e_3,e_1$ for $j\equiv0,1,2\pmod3$, respectively. The same phase order holds at $j=0,1,2$.

**Proof.** The literal trees $T_i=\rho^i\alpha$ satisfy $T_0=\alpha,T_1=\beta,T_{i+2}=\langle T_{i+1},T_i\rangle$. Their leaf counts give the stated $(m,n)$ and $N_k$. On the unit orthogonal leaves their ordered cross products cycle $e_1,e_2,-e_3$, so $T_{k+1+j}$ has the asserted sign and axis. Cassini, equivalently the sign reversal of $m^2+mn-n^2$ under $(m,n)\mapsto(n,m+n)$, gives $Q=-1$. Positive orthogonal homogeneity gives $q_0=s^{m+n-n^2/m}=s^{-1/m}$; the same-history transported formulas in 89.3 give $q_1=1$ and $q_2=s^{-1/m}$. The future formula follows from the actual norm recurrence. Finally $\Delta=s^2>d_0$, $\|b\|<1<L$, and $\|a\|\to s^{1+\varphi}=s^{\varphi^2}<L$. All sufficiently late sources therefore satisfy the simultaneous leaf and three-read bounds. No unit neutral member is used at $d_0>1$. This is the family of [supplier §81](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) with its original indexing. $\square$

For every $u\in S^2$, a single proper rotation of both leaves sending $e_2$ to $u$ yields a source whose designated future phase is $e^{-\lambda_kF_{j-1}}u$ for $j=3,6,9,\ldots$. Proper rotations commute with each ordered cross-product node, preserving the tree, preparation relation, determinant, read norms and complete future. They construct different legal sources; they do not supply an observer rotation or frame-calibration action.

Choose a fixed sufficiently late $k_0\equiv0\pmod6$ so that all these sources are legal and $\lambda_{k_0}\leq1$. Keep $k_i=k_0+6i$ and write $\lambda_i=\lambda_{k_i}$ for $0\leq i<K_N$, exactly while $F_{k_i+2}\leq N$. The identities

$$
13F_k\leq F_{k+6}=8F_{k+1}+5F_k\leq21F_k\quad(k\geq2)
$$

give $\lambda_i/\lambda_{i+d}\geq13^d$. Moreover $F_l\leq2^{l-1}$ for $l\geq1$ implies

$$
K_N\geq1+\left\lfloor\frac{\log_2N-k_0-1}{6}\right\rfloor
$$

whenever the right side is positive. Binet's formula, verified by the two initial values and recurrence, also gives $K_N=O(\log N)$; hence $K_N=\Theta_{L,d_0}(\log N)$. The designated sequence $F_2,F_5,F_8,\ldots$ starts at one, is unbounded and has consecutive ratios at most five, because $F_{l+3}=3F_l+2F_{l-1}\leq5F_l$ for $l\geq2$.

**Lemma 90.2 (a word spends finite total cap area).** Let a finite set $W$ of complete words cover every rotated source at all the $K_N$ levels within closed error $1/2$. For each usable word $w$, let $y_w(j)$ be its fixed vector answer and define

$$
A_i(w)=\bigcap_{j\in\{3,6,9,\ldots\}}
\{u\in S^2:\|e^{-\lambda_iF_{j-1}}u-y_w(j)\|\leq1/2\}.
$$

These necessary directional sets are closed and Borel, and $\bigcup_{w\in W}A_i(w)=S^2$ at every level. No measurability or continuity of an arbitrary source-aware encoder is required. If $\mu$ is normalized spherical area, then

$$
\sum_{i=0}^{K_N-1}\mu(A_i(w))<4
$$

for every word with a nonempty such set; an unused word contributes zero.

**Proof.** Let $r$ be the first level with $A_r(w)\ne\varnothing$. The first three possibly nonempty levels each contribute at most one. For $i=r+d$ with $d\geq3$, put $R=\lambda_r/\lambda_i\geq13^d$ and $t=R^{-1/2}<1/20$. Choose the first designated finite query with $\lambda_iF_{j-1}\geq t$. The starting exponent is $\lambda_i=\lambda_r/R\leq t$; the factor-five bound gives $t\leq\lambda_iF_{j-1}\leq5t$. At this query the faster amplitude satisfies $b\leq e^{-\sqrt R}\leq t$, and the slower amplitude satisfies $a\geq e^{-5t}\geq1-5t\geq3/4$.

A direction in $A_r(w)$ bounds the center norm $r_y=\|y_w(j)\|\leq1/2+t$. If $A_i(w)$ is nonempty, its feasibility gives $r_y\geq a-1/2\geq1/4$. Thus $v=y_w(j)/r_y$ exists, $ar_y\geq3/16$ and $a-r_y\geq1/2-6t>0$. Every $u\in A_i(w)$ satisfies

$$
(a-r_y)^2+ar_y\|u-v\|^2\leq1/4,
\qquad
\|u-v\|^2\leq
\frac{1/4-(1/2-6t)^2}{3/16}\leq32t.
$$

A unit-sphere cap of squared chord radius $\delta\leq4$ has normalized area $\delta/4$: its polar-height interval has length $\delta/2$, and the area element integrated over longitude is $2\pi$ times that height. Here $\delta=32t<4$, so $\mu(A_i(w))\leq8t\leq8\,13^{-d/2}$; empty sets obey the same bound. Therefore

$$
\sum_i\mu(A_i(w))\leq3+8\sum_{d\geq3}13^{-d/2}<4.
$$

For example $\sqrt{13}>3$ bounds the added series by $8\sum_{d\geq3}3^{-d}=4/9$. All ball inequalities use the closed radius exactly $1/2$. $\square$

**Corollary 90.3 (word-count lower).** Finite subadditivity at each covered level and Lemma 90.2 give

$$
K_N\leq\sum_{w\in W}\sum_i\mu(A_i(w))\leq4|W|.
$$

If every complete word has at most $B$ bits, including all source-dependent program variants, then $|W|\leq2^{B+1}-1$. Thus

$$
B\geq\log_2(K_N/4+1)-1
\geq\log_2\log_2N-O_{L,d_0}(1).
$$

An infinite worst-case length already satisfies the lower. A word failing to produce a required vector cannot cover that source. Granting arbitrary real vectors to every remaining decoder strengthens the lower-bound model. A fixed public phase direction instead has the constant midpoint predictor $u_j/2$ for every amplitude in $[0,1]$; the lower therefore needs the actual joint scale-and-direction bank, not an aligned scalar substitute.

## 91. Rational actual sources and source-size inversion

**Corollary 91.1 (exact rational subfamily).** The lower of Corollary 90.3, and hence the leading numerical-word law, persists when preparations and rotations are restricted to finite exact rational presentations.

**Proof.** Choose a positive rational $c$ with $\log\sqrt{d_0}<c<\log L/\varphi^2$. On the same Family A trees put $b_k=1+c/m$ and prepare

$$
(b_k^{m+n}e_1,b_k^{-n}e_2).
$$

Orthogonal homogeneity and $Q=-1$ give $q_0=q_2=b_k^{-1}$, $q_1=1$, the same signed phases, and rate $\lambda_k=\log(1+c/m)$. Also $\Delta=b_k^{2m}\to e^{2c}>d_0$ and $\|a\|\to e^{c\varphi^2}<L$, so all sufficiently late members are legal. The inequalities $c/(m+c)\leq\lambda_k\leq c/m$ give consecutive six-step rate ratios at least $13/2$ once $m\geq c$, hence at least six. Enlarge $k_0$ also for rates at most one.

The rational quaternion matrix of [supplier Definition 76.6](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) sends nonzero rational quadruples to rational proper rotations. Its continuous, surjective map from nonzero real quaternions to $SO(3)$ and density of rational quadruples make those rotations dense; their designated columns are dense in $S^2$. For each level a finite union of the closed $A_i(w)$ that contains every rational-source direction consequently covers the whole sphere. Repeat Lemma 90.2 with ratio six and $d\geq4$: the first four levels contribute at most four, $R\geq6^4>400$, and

$$
8\sum_{d\geq4}6^{-d/2}
=\frac{8/36}{1-1/\sqrt6}<1.
$$

Thus $K_N\leq5|W|$ and the same additive lower follows. The all-source upper below includes this subfamily. $\square$

This corollary restricts the source, not its production price. With fixed rational $c$, the unrotated preparation numerators and denominators can have $O(N\log(N+2))$ bits; any selected rational rotation adds its actual widths. No uniform presentation bound for all rational rotations, free rational instrument, or optimal production cost follows. Exact rational acquisition is the distinct paid contract of [supplier §§64,72–73,76.4,84](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md).

**Index reconciliation 91.2.** Family B in [supplier Theorem 66.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) and the precision lower of [supplier §71](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) is a different actual bank. It uses $T_k=\rho^k\alpha$, $k\equiv0\pmod6$, $m=F_{k-1}$, $n=F_k$, $d=n-m=F_{k-2}$, $N_k=F_{k+1}$ and preparation $(s^{n/d}e_1,s^{-m/d}e_2)$. Here $Q=+1$, equivalently $n^2-mn-m^2=-1$, and $q_0=1$, $q_1=q_2=e^{-z/d}$, $q_j=e^{-(z/d)F_j}$. Its phases are $e_1,e_2,-e_3$, with designated direction $e_1$. Family A has $T_{k+1}$, $Q=-1$, $F_{k+2}$ leaves and exponent $F_{j-1}$. These preparations, indices and signs are not interchanged. Both obey the principal domain eventually; Family A alone supplies the lower in §90.

**Corollary 91.3 (representation-stratum inversion).** Under Definition 89.1's numerical convention there are $c,C>0$ such that, for all sufficiently large integer bit caps $B$, the constructed $B$-bit representation covers every source with at most $\lfloor2^{c2^B}\rfloor$ leaves, while a $B$-bit cover of a sufficiently large $N$ stratum requires $N\leq2^{C2^B}$. Equivalently, the logarithm of the supportable worst-case source-size cap is $\Theta(2^B)$.

**Proof.** Apply the upper and lower in Theorem 89.2 and exponentiate twice, absorbing their fixed additive constants into $c,C$. The particular upper is constructed in §§92–93. $\square$

This inverts a family of representation statements. It supplies neither a source-size oracle nor a free double-exponential source generator. Arbitrarily required evidence invalidates an evidence-independent total-length inversion.

## 92. Complete endpoint words and the paid prefix alternative

**Definition 92.1 (terminal-scale endpoint mode).** Fix $\eta=2^{-10}$ and output precision ten as constants of this mode. Select $h\geq0$, $\sigma=2^{-h}$ with $\sigma\leq D\leq4\sigma$. A source-aware selection can take the largest dyadic at most $\min(D,1)$. Round each true loss to the nearest $\eta\sigma$ grid, half ties toward positive infinity, and clip to $[0,1]$. Store its nonnegative integer significand $a_1,a_2$. Store on the $\eta$ grid the nine coordinates, in phase order $3,4,5$ and coordinate order $1,2,3$, of

$$
A_3=x_3,\qquad A_4=Vx_1,\qquad A_5=UVx_2.
$$

Each true anchor has norm at most one. The semantic contract allows loss errors at most $\eta\sigma$ and anchor-vector errors less than $2\eta$; source-aware coordinate rounding gives the tighter error less than $\eta$. The acquired selection in §94 satisfies the broader contract.

The fixed eight-bit mode is $01101110$. Follow it by two unsigned thirteen-bit big-endian significands and nine twelve-bit big-endian offsets $n+1025$ for coordinate integers $-1025\leq n\leq1025$. These fields, including the mode, occupy exactly $142$ bits. The final field is the nonempty canonical binary expansion of $h+1$, including its leading one, through the existing complete-word end boundary. Thus, with $b=\lfloor\log_2(h+1)\rfloor+1$, the exact numerical length is $142+b$.

The parser consumes the entire finite word. It rejects a wrong mode, nonbinary symbols, incomplete fixed fields, an empty or leading-zero terminal scale, significands outside $[0,4097]$, offsets outside $[0,2050]$, reconstructed losses outside $[0,1]$, or $a_1+a_2\notin[512,8192]$. The loss-above-one test is $a_i\leq2^{h+10}$; bit-length comparison can avoid expanding a larger integer than needed for that test. Installation still pays all scale expansion.

The start of the scale field is fixed at bit $143$; its end is the supplied word end. No separately supplied length or control field occurs. A further binary suffix becomes scale digits; deleting some terminal digits may produce a different valid scale. This format promises parsing, not corruption detection from every suffix alteration. Incomplete fixed fields and an absent scale are rejected. Nonbinary trailers are invalid. The stronger prefix format below instead fixes the scale boundary internally and rejects all trailing data.

Every semantically selected word passes the tests. Each loss is at most $D\leq4\sigma$; the source-aware rounding and the acquired bounds in §94 give $a_i\leq4097$. The total true loss in grid units is between $1024$ and $4096$; two loss errors of at most one unit give the looser tested interval. True coordinates have magnitude at most one, and the raw acquired coordinate error is less than $\eta$ before half-grid rounding, giving $|n|\leq1025$. Clipping losses uses a grid containing both zero and one. These structural tests establish finite ranges, not source truth or provenance.

The reused $D\geq c_0/N$ and $\sigma\geq D/4$ give

$$
h\leq\log_2(4N/c_0),\qquad
142+b\leq\log_2\log_2N+O_{L,d_0}(1).
$$

Every source-dependent numerical bit is present; $E=1/2$, $\eta$ and the output precision are fixed mode constants. The represented $h$ is a finite integer, not an exact-real exponent. The fixed number of possibilities for the other fields and $O(\log N)$ possible scales also give an $O(\log N)$ upper on covering cardinality. Together with Corollary 90.3 and the evaluator in §93 this proves Theorem 89.2.

**Definition 92.2 (paid prefix-scale mode).** Use distinct header $01101101$. Before the same fixed numerical fields, encode the positive bit length $b$ by $\lfloor\log_2b\rfloor$ zeros followed by its canonical binary expansion. Then append the last $b-1$ digits of $h+1$, whose leading one is supplied by the grammar. Counting zeros and reading the corresponding binary digits determines $b$; exactly $b-1$ further digits determine $h$. The subsequent fixed fields have their original widths. The parser rejects any unfinished field, invalid range or trailing bit/symbol, and consumes the full finite input before its result.

This scale code is prefix-free: the initial positive gamma field determines the exact length of the remaining scale digits, and the numerical fields have fixed length. Its scale length is $b+2\lfloor\log_2b\rfloor$; its exact complete numerical length is

$$
142+b+2\lfloor\log_2b\rfloor.
$$

It therefore adds exactly $2\lfloor\log_2b\rfloor$ bits relative to the terminal-scale layout for the same fields. On the $N$ stratum its sufficient upper is $\log_2\log_2N+2\log_2\log_2\log_2N+O_{L,d_0}(1)$, with the same leading coefficient one. This is a specified sufficient prefix representation, not a prefix-free optimality theorem. Both modes have the identical semantic evaluator.

**Definition 92.3 (mandatory evidence and infrastructure).** Extend [supplier Definition 76.4](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)'s wrapper to accept either endpoint core in addition to its existing core modes. The wrapper consists of its eight-bit mode, gamma of the natural $M$, exactly $M$ literal evidence bits, and one core consuming the remaining framed word. The gamma convention is [supplier Definition 76.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). Invalid or truncated evidence and an invalid core are rejected. The exact additional length is

$$
8+2\lfloor\log_2(M+1)\rfloor+1+M.
$$

All mandatory source identity, certificates, transcripts, alternate programs or provenance are retained if the interface requires them. There is no assumed bound on $M$. A source-dependent alternate interpreter belongs to these paid fields, whereas one shared finite interpreter has a fixed additive description cost; transmitting that common description adds its actual fixed length. Parsing evidence does not certify truth. Numerical compression licenses discarding original evidence only under an interface that permits it. Theorem 89.2 is consequently not an $N$-only total upper for arbitrary evidence mandates.

## 93. All-future perturbation, finite arithmetic and complete queries

**Lemma 93.1 (uniform endpoint perturbation).** Let $\widehat U=1-a_1\eta\sigma$, $\widehat V=1-a_2\eta\sigma$ and let $\widehat A_r$ be the represented anchors from either endpoint mode. For every $j\geq3$, put

$$
r=3+(j\bmod3),\quad
R=\frac{F_{j-2}-F_{r-2}}2,\quad
S=\frac{F_{j-1}-F_{r-1}}2.
$$

Then $x_j=A_rU^RV^S$. The exponents are nonnegative integers, vanish at $j=3,4,5$, and thereafter satisfy $1\leq R\leq S\leq2R$. Under the semantic field contract, $\|\widehat A_r\widehat U^R\widehat V^S-x_j\|<14\eta$ for every $j$, including zero or unit bases.

**Proof.** This is the phase identity of [supplier §78](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md), with endpoint constants. Fibonacci parity has period three. At $j=r+3t$, $t\geq1$, the pairs $(S-R,2R-S)$ for $r=3,4,5$ are, respectively,

$$
\left(\frac{F_{3t}}2,\frac{F_{3t-1}-1}2\right),\quad
\left(\frac{F_{3t+1}-1}2,\frac{F_{3t}}2\right),\quad
\left(\frac{F_{3t+2}-1}2,\frac{F_{3t+1}-1}2\right).
$$

Their nonnegativity and the first later values $(R,S)=(1,2),(2,3),(3,5)$ prove the cone on all phases. Along the line segment between the true and represented bases the loss sum satisfies $D_t\geq D-2\eta\sigma\geq D/2$. For $f(u,v)=u^Rv^S$, polynomial derivatives on $[0,1]^2$ give

$$
|\partial_uf|+|\partial_vf|\leq3R(uv)^{R-1}
\leq\frac6{D_t}\leq\frac{12}D.
$$

Indeed $uv\leq1-D_t/2$, and $Rz^{R-1}\leq\sum_{l=0}^{R-1}z^l\leq(1-z)^{-1}$ for $0\leq z<1$. Integrating the derivative bound over base changes of at most $\eta\sigma$ gives scalar error at most $12\eta$. At the three initial anchors it is zero. True anchor norm is at most one, represented coefficient at most one, and anchor error less than $2\eta$, proving the claimed vector bound. Polynomial continuity covers $u=0,1$ or $v=0,1$ without division by a norm or normalization of noisy directions. $\square$

**Theorem 93.2 (finite numerical head and the entire tail).** Installation constructs the actual finite integer $T=32\cdot2^h$ and a Fibonacci list through the least $J\geq6$ with $F_{J-2}\geq2T+2$. For every $j\geq J$ return zero. For $3\leq j<J$, evaluate the represented coefficient by downward-rounded binary powers on a grid with $w=h+30$ fractional bits, multiply by the represented anchor, and round each output coordinate to the $\eta$ grid with half ties toward positive infinity. This fixed finite procedure has error less than $1/32$, hence less than $1/2$, for every required query.

**Proof.** For every $j\geq J$, $R\geq(F_{j-2}-2)/2\geq T$. Since $UV\leq1-D/2$ and $S\geq R$, the true vector norm is at most

$$
(UV)^R\leq e^{-RD/2}\leq e^{-16}<1/32.
$$

This controls the entire tail, not a finite sample. For the head, minimality gives $F_{J-2}<4T+4$ and the safe bound $R+S+1<8T+16<2^{h+9}$. Both represented bases are exact on the $2^{-w}$ grid, since their denominators divide $2^{h+10}$. A grid product of numerators $X,Y$ is $\lfloor XY/2^w\rfloor$, with downward error less than $2^{-w}$. Binary repeated squaring uses finitely many such products. Degree zero returns exactly one, including $0^0=1$.

Induction on multiplication degree bounds a degree-$n$ power error by $\max(n-1,0)2^{-w}$. Squaring adds twice the prior error and one rounding unit; multiplying positive-degree factors adds their errors and one unit, while multiplication by the exact unit creates no error. Products and rounded approximants remain in $[0,1]$. The combined two-power scalar error is at most $(R+S+1)2^{-w}<2^{-21}$. Represented anchors have norm less than two, and final vector grid rounding adds less than $\eta$. Lemma 93.1 therefore bounds head error by

$$
15\eta+2^{-20}<1/32<1/2.
$$

At $j=3,4,5$ the scalar is exactly one; zero bases, tiny anchors and all signs are included. Every operation is on finite integers or dyadics. No real logarithm, square root, sign, equality or orientation oracle is part of evaluation. $\square$

**Definition 93.3 (complete query and output).** Reuse [supplier Definition 76.8](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)'s finite transport: a leading $Q$, the nonempty canonical binary expansion of $j\geq3$, a semicolon, then end of input. Every character is consumed, including saturated or already invalid suffixes. Maintain the saturated value $v=\min(J,\text{prefix value})$, the residue modulo three, and finite framing, seen-digit, first-digit and invalidity flags. A binary digit $d$ updates $v$ to $\min(J,2v+d)$ and residue $r$ to $(2r+d)\bmod3$. The identity

$$
\min(J,2\min(J,n)+d)=\min(J,2n+d)
$$

proves the exact head index or tail decision and phase are preserved without storing an arbitrarily long integer. Reject missing $Q$, empty digits, a sign, nonbinary symbols, leading zeros, $j<3$, missing or additional semicolons, and trailing tokens. An invalid word also requires full consumption of the finite query before the finite error answer. One optional final transport newline may be consumed using one-character lookahead; a second newline is trailing error. Infinite streams are outside this finite-input contract.

The successful endpoint answer is the finite $V$ frame of [supplier §76.8](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md): gamma-coded precision ten, three gamma-coded signed dyadic numerators and a semicolon. Natural gamma is zeros followed by the binary expansion of the natural plus one, and the signed map is $2n$ for $n\geq0$, $-2n-1$ for $n<0$. The error frame is $\mathrm{ERR};$. The existing exact-zero mode has precision zero, and exact rational periodic modes use the $R$ frame of three reduced numerator/positive-denominator pairs. All symbols, precision, coordinates and output transport are paid. A symbolic power expression is not an emitted numerical answer. Full parsing, finite installation, finite head powering and finite output prove termination for every finite input; semantic accuracy is asserted for words satisfying the actual-source contract.

## 94. All-valid paid archive selection and the original acquisition boundary

**Theorem 94.1 (endpoint acquisition through the declared archive).** Suppose the extra archive of [supplier Definition 76.3](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) supplies the same three historical vectors and frame, with finite dyadic replies $y_i$ satisfying $\|y_i-x_i\|\leq2^{-b}$ simultaneously at every requested $b\geq1$. Replies may be correlated, off-image, nonorthogonal, zero, tiny or wrong in their computed sign. On every source of Definition 89.1, a finite interval selection terminates for every such valid name and yields either endpoint core with the semantic contract of Definition 92.1.

**Proof.** Use discovery precisions $b=1,2,4,\ldots$, put $e=2^{-b}$ and $l_i=[1-\|y_i\|^2]_0^1$ for $i=1,2$. True read norms are at most one, so squared-norm error is at most $(2+e)e\leq3e$; clipping is nonexpansive. Therefore

$$
D\in[\mathrm{lo},\mathrm{hi}],\quad
\mathrm{lo}=\max(0,l_1+l_2-6e),\quad
\mathrm{hi}=\min(2,l_1+l_2+6e).
$$

Stop discovery only if $\mathrm{lo}>0$ and $\mathrm{hi}\leq2\mathrm{lo}$. Select $\sigma$ as the largest dyadic at most $\min(\mathrm{lo},1)$ by finite rational comparisons, including equality. If $\mathrm{lo}\leq1$, then $\sigma\leq\mathrm{lo}<2\sigma$, while $D\leq\mathrm{hi}\leq2\mathrm{lo}\leq4\sigma$; if $\mathrm{lo}>1$, then $\sigma=1$ and $D\leq2$. Thus the same factor-four bin holds. No exact true-bin equality or real logarithm is inferred from approximate data.

Let $b_* =\max(1,\lceil\log_2(48/D)\rceil)$. For $b\geq b_*$, $e\leq D/48$, and the outward bounds give $\mathrm{lo}\geq D-12e\geq3D/4$ and $\mathrm{hi}\leq D+12e\leq5D/4$. Every valid name meets the guard there. The first successful doubling precision satisfies $b_c\leq2b_*$. Early success preserves the bin. Make exactly one final request at

$$
b_f=\max(b_c,h+14,28),
$$

even if a precision repeats. Then $e_f\leq\eta\sigma/16$ and $e_f\leq2^{-28}$. Round final clipped losses to the $\eta\sigma$ grid; their total error is less than $3e_f+\eta\sigma/2<\eta\sigma$.

For the first anchor put $w'=y_2\times y_1$ and $Z=\operatorname{sgn}(y_0\cdot w')w'$, using only a finite rational comparison. Bilinearity gives $\|w'-w\|\leq3e$ and

$$
|y_0\cdot w'-x_0\cdot w|
\leq e\|w\|+(q_0+e)3e\leq7e.
$$

If the sign is correct, anchor error is at most $3e$. If it is wrong or zero when the true sign is nonzero, the actual projection in 89.3 gives $q_2^2\leq|x_0\cdot w|\leq7e$ and $\|w\|=q_1q_2\leq\sqrt{7e}$. Hence

$$
\|Z-x_3\|\leq3e+2\sqrt{7e}\leq9\sqrt e.
$$

If the true scalar triple product is zero, the actual projection forces $q_2=0$, so $w=0$ and the same bound holds. This estimate is an ordinary proof; it requires no executable square-root or exact-real sign test. For the other raw anchors use $[\|y_2\|^2]_0^1y_1$ and $[\|y_1\|^2]_0^1[\|y_2\|^2]_0^1y_2$. Clipped-factor error at most $3e$ gives vector errors at most $4e$ and $7e$. At $b_f\geq28$ all three raw errors are less than $\eta$; nearest coordinate-grid rounding adds less than $\eta$. Thus every stored anchor error is less than $2\eta$, and the coordinate and significand bounds in 92.1 hold. Close the archive after compression; subsequent decoding uses only the complete word. $\square$

**Interface and finite framing 94.2.** This theorem reuses the truthful archive contract, not a new source Read. A reply is the $11001001$ mode, natural gamma($b$), and nine signed-numerator gamma fields with $|n_{ik}|\leq2^{b+1}$, no trailing data, and $y_i=n_i2^{-b}$. Its length is at most $18b+2\log_2(b+1)+80$. Arity, precision, range, nonbinary, truncation and trailing-data checks establish syntax only; same-history truth and accuracy remain supplier premises. Repeated requests refer to the same immutable name.

The outgoing grammar is exactly [supplier §76.3](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)'s discovery header $01011010$ and final header $01011011$ followed by natural gamma($b_f$). A session starts with stored precision one; each discovery serves it and doubles it. Zero or more discovery commands, exactly one final command and closure are allowed. Unknown, unfinished, zero-final-precision or trailing requests are invalid. Schedule state, command parsing, doubling, setup, capture and archive storage are paid. A mathematical precision callback alone does not establish this wire bound.

**Original finite replies and certificates 94.3.** The source-aware upper in Theorem 89.2 preserves the once-only finite-reply impossibility of [supplier Theorem 70.3](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) and [supplier §82](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) on the unrestricted plateaus at $0<E\leq1/2$. On the unbounded neutral-free bank, a hypothetical finite adaptive three-report path with positive reply slack has common replies for sufficiently late Family B histories with small opposite proper rotations, together with a fixed contracting member. Fixed-query limits followed by the contracting tail would require one radius-$E$ ball to contain $0,u_+,u_-$. For a small positive angle $2\theta<\pi/2$, that ball needs radius $1/(2\cos\theta)>1/2$. The contradiction uses jointly realizable sources and the same finite transcript. For nearest-true-dyadic replies, small rotations and deficits must lie inside the common grid cells, as checked in [supplier §§70,82](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md); a different deterministic production rule needs its own fiber verification. Exact rational replies and source-dependent truthful certificates lack this noisy finite-fiber premise.

A single issued triple can use the same selector only if its outward guard holds and $b\geq\max(h+14,28)$; otherwise it rejects insufficient precision and makes no further request. A truthful represented pre-read gap, size or domain certificate can ensure sufficient precision before the original three Reads. Its issuance, binding, validation and mandatory retained evidence have their actual costs. For the size certificate of [supplier §67.3](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md), with $\overline N\geq m+n$ and rational $1<d_-\leq d_0$, put $z_-=(d_--1)/(2d_-)$, $t_-=z_-/\overline N$ and $\kappa=1-t_-/2$. That theorem gives $q_2\leq e^{-t_-}\leq(1+t_-)^{-1}\leq\kappa<1$, supplying a paid positive gap for a fixed reply schedule.

More explicitly, a truthful rational bound $q_2\leq\kappa<1$ gives $D\geq g=1-\kappa^2>0$. Set $h_{\max}=\lceil\log_2(4/g)\rceil$ and choose the single reply precision $b=\max(1,\lceil\log_2(48/g)\rceil,h_{\max}+14,28)$. The proof in 94.1 gives the guard for every valid triple, and its selected $h\leq h_{\max}$ because $\sigma\geq D/4\geq g/4$. Thus the fixed-reply selector accepts without another request. Each displayed ceiling is determined by finite dyadic comparisons with the represented positive rational $g$; it is not a real-logarithm input operation. A bare integer $h$ or $\overline N$ proves no source truth. The exact finite rational instrument is a separate paid contract. A nonzero sensor error floor cannot provide arbitrarily refining names. Original once-issued replies do not become an archive after Stop.

## 95. Retention, acquisition, installation and source costs

**Proposition 95.1 (a jointly specified sufficient resource profile).** Write $B_{\max}=b_f$ and $\ell$ for the full finite query length. For the endpoint modes, with finite streaming inputs and schoolbook arithmetic, the following resources are charged separately.

| Resource | Sufficient bound or actual charge |
|---|---|
| Complete numerical word | Exactly $142+\operatorname{bitlength}(h+1)$ bits in terminal mode; prefix mode adds exactly $2\lfloor\log_2\operatorname{bitlength}(h+1)\rfloor$ |
| Mandatory evidence and alternate programs | Actual complete widths and wrapper framing from 92.3; no assumed bound |
| Common interpreter | Actual fixed description, transport if required, and installation |
| Archive maximum precision and canonical raw returned bits | $B_{\max}=O(h+1)$ and total $O(h+1)$ bits |
| Archive calls | $O(\log(h+2))$ discovery/final calls |
| Outgoing two-command frames | $O(\log(h+2))$ bits; actual authentication and other evidence add their widths |
| Downstream encoder | $O((h+1)^2\log(h+2)+|\mathrm{word}|)$ bit time, $O(h+1)$ arithmetic scratch plus actual reply/evidence buffers |
| Installed Fibonacci cache | $O((h+1)^2)$ bits, with $O(h+1)$-wide integers |
| Setup | $O(|\mathrm{word}|+(h+1)^3)$ conservative bit time |
| Full query parsing | $O(\ell(1+\log(h+2)))$ bit time and $O(\log(h+2))$ streaming state |
| Head arithmetic | $O((h+1)^3)$ bit time and $O(h+1)$ extra scratch in addition to installation |
| Tail arithmetic | Constant only after consuming the entire query |
| Endpoint numerical output and buffer | Fixed finite width, plus actual frame/transport and any evidence output |
| Source and archive production | Actual construction, precision, storage, action, latency and evidence costs; no bound inferred from word length |

**Proof.** The certified bin makes $h$ differ from $\log_2(1/D)$ by at most a fixed constant when $D\leq1$; $D>1$ gives bounded $h$. The discovery bound in 94.1 and final choice therefore yield $B_{\max}=O(h+1)$. Scheduled precisions sum to less than $2b_c$; including the final request they sum to at most $3B_{\max}$. Reply lengths are linear in precision plus logarithmic framing, so total canonical returned bits are $O(h+1)$. If there are $d$ discovery calls, the exact outgoing charge is $8(d+1)+2\lfloor\log_2(B_{\max}+1)\rfloor+1$, and $d=1+\log_2b_c$. Archive precision state has $O(\log(h+2))$ bits. If every precision is instead independently gamma-coded, the separately safe outgoing bound is $O(\log^2(h+2))$; the improved bound uses the actual two-command grammar. Supplier production and additional padded evidence are excluded from canonical numerical reply bounds, not erased.

There are a fixed number of $O(b)$-wide rational square, cross and dot operations per call. Summing their schoolbook costs and including scale comparisons gives the conservative encoder bound. Exact rational instruments add actual input numerator/denominator widths. Installation has $J=O(h+1)$ Fibonacci entries, each $O(h+1)$ bits, and constructs $2^h$ rather than treating its short exponent description as free storage. The arithmetic grid has $h+30$ fractional bits. A head uses $O(h+1)$ binary-power multiplications on $O(h+1)$-wide integers. These facts give the cache, setup, scratch and conservative time bounds. Query parsing uses the finite saturation recurrence, reads every character and stores only an $O(\log J)$-bit value and finite flags. Output coordinate integers are bounded at the fixed endpoint precision. Discarding the installed list requires paying installation again. $\square$

On the proof stratum this profile has $O(\log N)$ requested precision/raw receiving bits, $\log_2\log_2N+O(1)$ retained numerical bits, $O((\log N)^2)$ installed cache bits and $O((\log N)^3)$ setup/head work. These are sufficient bounds for one profile, not simultaneous optima. Retaining the cache makes resident memory grow as $O(h^2)$; the short word does not bound installed memory by $O(\log h)$.

The narrower maximum-precision lower in [supplier §71.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) remains distinct. Along its Family B, with $v_k=e^{-z/d}$, a valid ordinary name may return the unit history whenever $2^{-b}\geq1-v_k$. With fixed public inputs and no source-dependent advice or certificate, a reliable endpoint algorithm cannot stop on a finite all-unit prefix, by the three-point fiber proof. It must request $b>\log_2(1/(1-v_k))=\log_2N_k+O(1)$. Together with the archive upper this gives worst-name maximum precision $\Theta(\log N_k)$ on that bank. Unit-scale canonical positional/gamma replies at that precision have comparable width, but another compressed supplier format can encode unit responses differently. This is neither a format-independent received-bit lower, a retained-bit lower, nor a general acquisition optimum when separately paid advice, certificates or rational instruments are permitted.

If the original tree has counts $(m,n)$, its three literal versions have $m+n$, $m+2n$ and $2m+3n$ leaves. Their literal evaluations use $4m+6n-3$ cross products. Actual tree syntax, scanning, substitution, evaluation stack, preparing $(a,b)$ at the required accuracy, original observation, common-frame binding, archive capture and truthful approximation production, certificate issuance/verification, closure, authentication, output and latency retain their own costs. The cross-product count alone is not a bit-time bound, and it is not an observer count port. Receiving and discarding high-precision digits reduces retention while leaving acquisition work paid.

## 96. Exact regime reuse and the remaining recovery scope

**Regime boundary 96.1.** Retain the standing $L,H>0$ and $0<d_0<L^4$, put $D_{\mathrm{crit}}=L^{2/\varphi^2}$, and use the complete ten-row classification of [supplier §§24–32,53,65,84](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). Theorem 89.2 refines the endpoint left open in [supplier §§82,85,88](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) only on row five with $d_0>1$. It changes none of the other hypotheses or proofs.

| Row | Original condition | Reused whole-future class |
|---|---|---|
| 1 | $L<1$, any $H>0$ | Linear contraction |
| 2 | $L=1$, $H<1$ | Linear contraction |
| 3 | $L=1$, $H\geq1$; standing $d_0<1$ | Plateau with neutral sources |
| 4 | $L>1$, $d_0<D_{\mathrm{crit}}$, $H<1$ | Linear contraction |
| 5 | $L>1$, $d_0<D_{\mathrm{crit}}$, $H=1$ | Plateau; neutral exactly when $d_0\leq1$ |
| 6 | $L>1$, $d_0<D_{\mathrm{crit}}$, $H>1$ | Growth |
| 7 | $L>1$, $d_0=D_{\mathrm{crit}}$, $H\leq1$ | Zero future, including $H=1$ |
| 8 | $L>1$, $d_0=D_{\mathrm{crit}}$, $H>1$ | Growth |
| 9 | $L>1$, $d_0>D_{\mathrm{crit}}$, $H<H_*$ | Zero future |
| 10 | $L>1$, $d_0>D_{\mathrm{crit}}$, $H\geq H_*$ | Growth, including attained equality |

The actual supported counts and finite three-line threshold optimization are precisely those of [supplier §§18–19,53,65.4](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md); $H_*$ is their attained threshold. In particular $H_*(6,4)=32/27$ is reused at the eight-leaf $(3,5)$ source with preparation $(6e_1,e_2/3)$ and reads $(0,0,8/9)$, $(-32/27,0,0)$, $(0,-256/243,0)$, followed by $(0,0,8192/6561)$. Its finite coverage proof and exact certificate establish the equality case. No new enumeration, threshold or arbitrary-real effective equality classifier is needed here. Exactly rows one, two and four are linear; their finite-reply acquisition requires the represented truthful rational contraction bounds of [supplier §§73,84](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md).

**Neutral and tolerance boundary 96.2.** The one-leaf witnesses of [supplier §82](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) retain $C_N(1/2)=\infty$ already at $N=1$ in the neutral-containing plateaus. In row five with $d_0\leq1$, including equality, use $t=\beta$ and $(e_1/r,re_2)$, $1/L<r<1$: $\Delta=1$, $q_0=q_2=r$, $q_1=1$, $q_j=r^{F_{j-1}}$, with neutral member $r=1$. In row three use $t=\alpha$, $(\lambda e_1,\lambda e_2)$, $d_0^{1/4}\leq\lambda<1$, and its unit neutral limit. Proper rotations of each common preparation preserve legality. The finite-alphabet argument in [supplier §§70,82](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) uses recurrence within a finite alphabet, not recurrence forced by countably many variable-length words. It allows an individually finite source-aware word for every source and every positive error.

The archive selector remains pointwise total whenever $D>0$. It cannot be total on an actual neutral name at $0<E\leq1/2$ without extra truthful neutral information: any finite queried prefix with positive slack extends to nearby rotated contracting one-leaf names, and the same three-point contradiction applies. A tree/count certificate alone cannot distinguish these fixed-tree worlds. A truthful neutral certificate or an exact rational equality comparison is a different paid interface. No neutral detector for arbitrary real names follows from syntax.

[supplier Theorem 81.1](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) is retained exactly: for fixed $E_0<1/2$, uniformly $0<E\leq E_0$ and sufficiently large $N$ in Definition 89.1's domain, the numerical law is $\Theta_{L,d_0,E_0}(1+\log(1/E)+\log\log(N+2))$. Its strict separation does not supply the endpoint proof. For either full plateau over all source sizes, [supplier §83](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md)'s separate $E=1/2+\tau$, $0<\tau\leq1/8$, orientation alphabet has $\Theta(\log(1/\tau))$ bits as $\tau\downarrow0$, with its finite rational quaternion/reflection grammar, paid acquisition and output slack. This is not a lower for every fixed $N$ stratum; larger errors may reuse $\tau=1/8$. The minimum enclosing radius of $\{0,u,v\}$ remains $1/(2\cos(\theta/2))$ for $0\leq\theta\leq\pi/2$ and $\sin(\theta/2)$ for $\pi/2\leq\theta\leq\pi$. The obtuse circumradius formula and the countable-sequence recurrence inference are not valid routes.

At $E=0$, or for one word answering all tolerances, a legal nonzero source's uncountable rotated $x_3$ sphere gives the exact-value obstruction of [supplier §84](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). It applies to strata containing that witness. Zero futures remain exact-zero exceptions. Positive source-dependent tolerances require their finite represented tolerance/promise and paid acquisition; they are not forbidden merely by countability. In growth rows the full real class instead has an uncountable actual proper-rotation family with pairwise infinite future distance, defeating individually finite words even with finite source-dependent error bounds. Exact finite-rational histories remain the separately paid restricted exception in all ten regimes, with their actual query-dependent arithmetic and output widths. Persistent real names remain an input port, not a closed word.

**Zero and envelope boundary 96.3.** Zero rows have a constant exact-zero numerical word, including at $E=0$, while original actions, source evidence and initial read envelopes remain charged. Zero future does not imply $x_0=0$ or a unit initial bound. The witness of [supplier §§73.2–73.3,87](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) is $t=\langle\alpha,\langle\beta,\langle\alpha,\beta\rangle\rangle\rangle$, $a=(3,0,0)$, $b=(7/24,4/3,0)$, with $L=3,H=7/2,d_0=16$, $x_0=(0,0,-7/2)$ and $x_j=0$ for $j\geq1$. Its $H_*=4$ places it in row nine. A truthful represented envelope $\overline H\geq\max(1,H)$ supplies the original finite reply alphabet. The unit-read archive grammar of §94 is asserted only under its unit-read hypotheses and is not extended to this initial report.

**Representation and autonomous recovery 96.4.** Sum squared losses, maximum squared loss, raw deficits with normalized directions and common logarithmic rates remain alternative coordinates of the same actual response at the scopes of [supplier §§78,85–86](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md). The sum-loss perturbation is $12\eta$; the tolerant max-loss version is $24\eta$. Literal exact powers can have exponentially large numerical-scale width. Rounded powering in §93 supplies one sufficient polynomial resource profile; finite Taylor and binomial alternatives retain their separate accuracy, acquisition and normalization costs. None is a scalar optimum over all supplier, evidence, cache, time and output coordinates.

The published autonomous NEXT contract retains its own acquired-state and external-retained-context assumptions. Source-aware word selection is not an autonomous observer transition. The endpoint archive is an additional paid history port, while certificates and exact rational instruments are different interfaces. The representation theorem therefore proves neither optimal autonomous total memory nor a new original all-future acquisition capability. It also leaves the full intermediate finite-noise risk curve, optimal acquisition/work/cache/output/source-production costs, arbitrary-real threshold classification, physical preparation/frame realization and the persistent mutual recovery of space, time, boundary and memory unresolved.

**Sources and proof scope 96.5.** The endpoint cap incidence and complete end-framed scale combination are repo-derived ordinary mathematical refinements. The actual family, integer bridge, phase algebra, finite loss representation, archive contracts and other regime proofs are reused at the explicit section references above. Classical cross-product identities, Fibonacci/Cassini/Binet formulas, spherical cap integration, finite counting, quaternion rotations and integer prefix coding are prior mathematics. The represented-space and recurrence literature in [supplier §88](RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md) supplies background only at its stated hypotheses; no generic entropy, scalar Hankel, discounted metric or independent-product result is substituted for this actual-source endpoint. No worldwide novelty, exhaustive literature search, new Lean/kernel verification, physical validation or completion of the persistent recovery goal is claimed. The universal statements here rest on the ordinary proofs; no new finite mathematical diagnostic count is used as their evidence.

## 追加锚（本行以下为增补区）

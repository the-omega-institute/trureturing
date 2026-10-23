# KBonacci self-calibrating boundaries continuation

This volume continues the self-calibrating boundary results after Section 37. It retains the parent definitions and notation; Sections 38–41 below belong to this continuation.

## 38. Local self-calibration from window and prime-support side information

This section uses exactly the numerical source $W$ and prime-divisibility observations of Section 39. Its conclusions are `repo-derived` deductions from Theorem 37.2 and elementary finite-set and divisibility arguments. They are ordinary mathematical theory prose, with no claim of Lean/kernel verification or literature priority. The added information is an explicit source relation; it is not inferred for free from the old probe bits.

**Definitions (labeled source and calibration intervals).** Let $\mathbb P$ denote the positive primes and $\mathbb N_0$ the nonnegative integers. Retain the Fibonacci recurrence $F_0=0$, $F_1=1$, $F_{j+2}=F_{j+1}+F_j$ and write

$$
\begin{aligned}
L_r&=\lceil F_r/10\rceil,& U_r&=\lfloor F_r/5\rfloor,&
I_r&=[L_r,U_r]\cap\mathbb Z,\\
X&=\{(r,g):r\in\mathbb P,\ g\in I_r\},&
N(r,g)&=1+F_rg,& \Omega(r,g)&=\omega(N(r,g)).
\end{aligned}
\tag{38.1}
$$

Thus $W_r=\{N(r,g):g\in I_r\}$ and $N[X]=W=\bigcup_{r\in\mathbb P}W_r$, where an interval with $L_r>U_r$ is empty. The target $\omega(n)$ counts distinct prime divisors, with $\omega(1)=0$. For finite $S\subset\mathbb P$, write $d_S(n)=(\mathbf1_{p\mid n})_{p\in S}$ and $\rho_S(n)=\omega(n)-\sum_{p\in S}\mathbf1_{p\mid n}$ for the probe record and the unobserved support size. For $S=\varnothing$ there is one empty pattern, its sum is zero and $\rho_S=\omega$.

The labels in $X$ keep the generating window explicit: if two windows share a numerical value, their labeled sources remain distinct. A numerical observation on $W$ is pulled back along $N$. Supplying $r$ means supplying the label, or the promise $n\in W_r$; it does not assume a unique index determined by $n$. None of these labels is a phase or an endpoint fee from the earlier sections.

For any observation $o:X\to Y$ and any occupied cell $C_y=o^{-1}(\{y\})\ne\varnothing$, define

$$
L_o(y)=\min_{x\in C_y}\Omega(x),\qquad
U_o(y)=\sup_{x\in C_y}\Omega(x)\in\mathbb N_0\cup\{+\infty\}.
\tag{38.2}
$$

The minimum exists because the values are nonnegative integers; a finite supremum is also attained. No calibration interval is assigned to an empty cell. The interval $[L_o(y),U_o(y)]$ encloses the possible target values; it need not contain only attainable values. A sound finite upper certificate at $y$ is a finite number $c(y)$ with $\Omega(x)\le c(y)$ for every $x\in C_y$. Such a certificate exists exactly when $U_o(y)<\infty$. An exact decoder $D:o[X]\to\mathbb N_0$ with $D(o(x))=\Omega(x)$ exists exactly when every occupied cell has one $\Omega$ value, equivalently $L_o(y)=U_o(y)$. These are set-theoretic criteria, not computability assertions.

Say $\widetilde o$ refines $o$ when $o=h\circ\widetilde o$ for some map $h$ on the attained observations. For every occupied refined cell with $y=h(\widetilde y)$,

$$
L_o(y)\le L_{\widetilde o}(\widetilde y)
\le U_{\widetilde o}(\widetilde y)\le U_o(y).
\tag{38.3}
$$

Indeed, its sources form a nonempty subset of $C_y$, so taking the minimum and supremum gives these inequalities. The decoding criteria follow by constancy on each fibre, and the certificate criterion follows by the definition of supremum. If $o$ includes a finite probe record $d_S(N(x))=b$, then the observed contribution gives the sound lower bound

$$
\sum_{p\in S}b_p\le L_o(y)\le\Omega(x)\le U_o(y)
\qquad(x\in C_y).
\tag{38.4}
$$

This lower bound need not be sharp. Refinement can raise the lower endpoint and lower the upper endpoint, while exactness requires the endpoints to coincide.

**Theorem 38.1 (The index-fibre criterion and finite completion of probes).** Let $\alpha:\mathbb P\to A$ be any index-side observation, let $S\subset\mathbb P$ be finite, and put

$$
\begin{aligned}
o_{\alpha,S}(r,g)&=(\alpha(r),d_S(N(r,g))),\\
C_{a,b}&=\{(r,g)\in X:\alpha(r)=a,\ d_S(N(r,g))=b\},\\
P_a&=\{r\in\mathbb P:\alpha(r)=a,\ I_r\ne\varnothing\},\\
P_{a,b}&=\{r\in P_a:\exists g\in I_r,\ d_S(N(r,g))=b\}.
\end{aligned}
\tag{38.5}
$$

Here $P_a$ is compatible with the side information, while $P_{a,b}$ is compatible with the entire observed record. For every occupied $C_{a,b}$,

$$
\begin{aligned}
U_{o_{\alpha,S}}(a,b)<\infty
&\ \Longleftrightarrow\ P_a\text{ is bounded}
\ \Longleftrightarrow\ P_a\text{ is finite}\\
&\ \Longleftrightarrow\ P_{a,b}\text{ is bounded}
\ \Longleftrightarrow\ P_{a,b}\text{ is finite}.
\end{aligned}
\tag{38.6}
$$

If $P_a$ is finite, it is nonempty under this occupancy assumption, and

$$
B_a=\max_{r\in P_a}(1+F_rU_r),\qquad
U_{o_{\alpha,S}}(a,b)\le\lfloor\log_2 B_a\rfloor<\infty.
\tag{38.7}
$$

Given an explicit valid integer bound $B\ge B_a$, a finite additional set of prime queries recovers $\Omega$ exactly: with $Q_B=\{p\in\mathbb P:p\le B\}$,

$$
\Omega(x)=\sum_{p\in Q_B}\mathbf1_{p\mid N(x)}
\qquad(x=(r,g)\in X,\ \alpha(r)=a).
\tag{38.8}
$$

The added queries are only those in $Q_B\setminus S$. Exact recovery from $(a,b)$ itself, without these additional answers, still requires a singleton $\Omega$ fibre, or $L_{o_{\alpha,S}}(a,b)=U_{o_{\alpha,S}}(a,b)$.

**Proof.** A subset of the positive integers is bounded if and only if it is finite. If $P_a$ is finite, its finitely many windows contain finitely many labeled sources, and every one has $1\le N(r,g)\le B_a$. The product of the distinct prime divisors of any positive integer $n$ divides $n$ and is at least $2^{\omega(n)}$. Therefore $2^{\Omega(r,g)}\le N(r,g)\le B_a$, giving (38.7). Every prime divisor is at most $N(r,g)\le B$, which proves (38.8).

Conversely, suppose $P_a$ is unbounded. Fix any $b\in\{0,1\}^{S}$ and any integer $K\ge1$. Choose $r\in P_a$ with $r\ge R(S,K)$, where $R(S,K)$ is the threshold of Theorem 37.2. That theorem applies to this chosen prime index, however sparse $P_a$ is, and supplies $g\in I_r$ with

$$
d_S(N(r,g))=b,\qquad
\Omega(r,g)=\rho_S(N(r,g))+\sum_{p\in S}b_p
\ge K+\sum_{p\in S}b_p.
\tag{38.9}
$$

Thus every pattern has an occupied cell and both its residual support and its total support are unbounded. This proves the reverse implication for $P_a$. In addition, Theorem 37.2 with $K=1$ gives

$$
P_a\setminus P_{a,b}\subseteq\{r\in\mathbb P:r<R(S,1)\}.
\tag{38.10}
$$

Only finitely many indices can be lost when the bits are imposed. Since $P_{a,b}\subseteq P_a$, their boundedness and finiteness are equivalent, proving (38.6). This does not assert that every small window realizes every pattern: empty windows have already been removed, and primes dividing $F_r$ can force zero bits in the remaining small windows. The exactness assertion is the fibre criterion in (38.2), not a consequence of finiteness alone.

**Corollary 38.2 (The adaptive obstruction inside an infinite index cell).** Fix $a$ with $P_a$ infinite. Consider a deterministic procedure whose only source information is $\alpha(r)=a$ and answers to prime-divisibility queries about $N(r,g)$. Its next prime, stopping decision and output may depend on $a$, the preceding transcript and parameters common to this entire index cell. Every finite realized transcript leaves $\Omega$ unbounded on its compatible sources. Hence no such transcript can be a sound leaf outputting a finite upper bound, or certifying $\Omega\le c$ for finite $c$.

**Proof.** Deduplicate the finitely many queried primes into $S$ and their consistent answers into $b$. All sources in $C_{a,b}$ follow the same path: equal earlier answers force the same next query or stopping decision. Theorem 38.1 makes this cell's $\Omega$ values unbounded, so one finite upper output cannot be sound for all of them. The argument includes the empty transcript, repeated queries and a source-dependent number of queries; it does not assume a uniform bound on transcript length. It permits halting with no finite upper claim, and says nothing about procedures supplied with further source information. With constant $\alpha$, it recovers the global obstruction of Section 39. With exact $r$, the compatible index set is a singleton and this obstruction no longer applies.

**Proposition 38.3 (A fixed window and finite probes need not determine $\omega$).** For the exact supplied index $r=13$ and $S=\{2,5\}$, one occupied observation cell contains two different $\omega$ values:

$$
\begin{aligned}
F_{13}&=233,& I_{13}&=[24,46]\cap\mathbb Z,\\
5593&=1+233\cdot24=7\cdot17\cdot47,& \omega(5593)&=3,\\
6059&=1+233\cdot26=73\cdot83,& \omega(6059)&=2.
\end{aligned}
\tag{38.11}
$$

Both integers have $d_{\{2,5\}}=(0,0)$. Thus exact index information supplies finite upper calibration without, in general, exact target recovery from the index and the existing probes.

**Proof.** The Fibonacci recurrence gives $F_{13}=233$; hence $L_{13}=\lceil233/10\rceil=24$ and $U_{13}=\lfloor233/5\rfloor=46$. The index $13$ is prime and both $24,26$ lie in the interval. Direct multiplication gives the two factorizations in (38.11). Trial division by primes not exceeding each factor's square root verifies that $7,17,47,73,83$ are prime; the only trial primes needed are among $2,3,5,7$. The factors in each product are distinct. Both products are odd and neither is a multiple of $5$, giving the same zero bits and the stated unequal counts. The window magnitude bound is

$$
1+F_{13}U_{13}=1+233\cdot46=10719,
\qquad 2^{13}\le10719<2^{14}.
\tag{38.12}
$$

For $o=o_{\mathrm{id},\{2,5\}}$ and $y=(13,(0,0))$, it follows that $L_o(y)\le2<3\le U_o(y)\le13$. These inequalities exhibit a nonzero exactness gap, without claiming either endpoint is sharp.

**Proposition 38.4 (Four sufficient forms of side information).** In the source $X$, each of the following supplied relations gives finite upper calibration on every occupied cell to which the relation applies. The stated decoder uses further prime-divisibility answers; none of these relations alone is asserted to determine $\Omega$.

1. **Exact window label.** A supplied nonempty index $r$ gives $N\le B_r=1+F_rU_r$ and $\Omega\le\lfloor\log_2B_r\rfloor$. Querying all primes at most $B_r$ gives the exact count.
2. **Bounded index bucket.** A bucket value $a$ supplied with a known positive integer bound $R(a)$ and the promise $r\le R(a)$ gives a finite window union. For an occupied bucket,

   $$
   N\le M_a=1+F_{R(a)}\lfloor F_{R(a)}/5\rfloor,
   \qquad \Omega\le\lfloor\log_2M_a\rfloor.
   \tag{38.13}
   $$

   Querying all primes at most $M_a$ gives the exact count. For example, the supplied bucket number $j$ with $2^{j-1}<r\le2^j$ has the available bound $R(j)=2^j$.
3. **Magnitude bound.** A supplied integer $M\ge1$ and the promise $1\le N\le M$ give $\Omega\le\lfloor\log_2M\rfloor$. Querying all primes at most $M$ gives the exact count, without supplying a generating index.
4. **Certified complete prime-support envelope.** A supplied finite set $T\subset\mathbb P$ and the sound promise

   $$
   \{p\in\mathbb P:p\mid N(x)\}\subseteq T
   \tag{38.14}
   $$

   for every source $x$ compatible with the supplied information give $\Omega\le|T|$. The set may contain primes that do not divide the actual integer; completeness means that no prime divisor lies outside it. For an additional occupied probe record $d_S(N)=b$, set $A_b=\sum_{p\in S}b_p$. Then

   $$
   A_b\le\Omega\le A_b+|T\setminus S|\le|T|.
   \tag{38.15}
   $$

   Querying every prime in $T\setminus S$ gives $\Omega=\sum_{p\in T}\mathbf1_{p\mid N}$ exactly.

**Proof.** The first relation is Theorem 38.1 with $\alpha(r)=r$. For the second, occupied windows have $r\ge5$: $I_2=I_3=\varnothing$, while $I_5=\{1\}$. Fibonacci monotonicity therefore gives $F_r\le F_{R(a)}$ and $U_r\le\lfloor F_{R(a)}/5\rfloor$, proving (38.13). The finite prime-query formula follows as in (38.8). For the third, $2^{\Omega}\le N\le M$ gives the bound and every prime divisor is at most $M$. For the fourth, occupancy forces $b_p=0$ at any queried prime outside $T$; the observed divisors contribute $A_b\le|S\cap T|$, and all remaining distinct divisors lie in $T\setminus S$. This proves (38.15) and the decoding formula.

Empty promises create no occupied cell. In particular, $T=\varnothing$ would force $N=1$ for a positive integer, but no source in $X$ has that value: nonempty windows have $g\ge1$ and $F_r\ge5$. A bound $M=1$ is likewise empty here, although the convention $\omega(1)=0$ makes the general counting formula consistent. The completeness of $T$ and the magnitude or index bounds are source promises; a finite list of tested primes by itself certifies none of them on all of $W$.

The finiteness in Theorem 38.1 is distinct from effectively available decoder data. An arbitrary map $\alpha$ need not provide a way to enumerate its finite fibre $P_a$, compute $B_a$, or find a valid upper bound from $a$. A supplied numerical index bound or magnitude bound does provide such finite data. In the support case the decoder needs the complete finite list $T$, not merely an assertion that the actual integer has finitely many prime divisors, which is already true for every $N$. Given these data, finite enumeration and the indicated finite queries suffice; no factoring-efficiency, polynomial-time, uniform query-budget or physical-resource bound is asserted.

**Proposition 38.5 (Finite-valued side observations and the global/local distinction).** A finite-valued side observation does not automatically calibrate every source. More precisely, for any finite-valued $\beta:X\to E$, any finite $S\subset\mathbb P$ and every $b\in\{0,1\}^{S}$, at least one occupied joint cell

$$
\{x\in X:\beta(x)=e,\ d_S(N(x))=b\}
\tag{38.16}
$$

has unbounded $\Omega$. For finite-valued index-side $\alpha$, at least one $P_a$ is infinite, and in that same index cell every finite probe pattern has unbounded $\Omega$ and Corollary 38.2 applies. Nevertheless, individual cells selected by additional source relations can have finite upper bounds, as in Proposition 38.4. There is no finite constant bounding $\Omega$ on all of $X$, or $\omega$ on all of $W$.

**Proof.** For each fixed $S,b$, Theorem 37.2 makes the pullback of $W_{S,b}$ to $X$ unbounded in $\Omega$. Its partition by the finitely many values of $\beta$ must have an unbounded part: otherwise the maximum of the finitely many finite bounds on its occupied parts would bound the whole fibre. For index-side $\alpha$, infinitely many prime indices have nonempty windows, and finitely many finite sets cannot cover them. An infinite $P_a$ therefore exists and Theorem 38.1 applies. Taking $S=\varnothing$ in Theorem 37.2 rules out a global constant. These statements do not say that every cell of an arbitrary $\beta$ is unbounded, nor extend the index-only criterion to arbitrary restrictions on $g$ or $N$.

**Scope 38.6 (The self-calibration bridge and its remaining exactness gap).** Section 37 diagnoses the original probe fibres: their upper endpoint is infinite at every finite record, including adaptive records. Adding a sound relation about the window, index range, magnitude or complete support refines those fibres. Theorem 38.1 classifies exactly when index-side refinement makes the upper endpoint finite, and Proposition 38.4 gives explicit finite decoding data for four sufficient relations. The interval $[L_o(y),U_o(y)]$ measures what remains unresolved: finite $U_o(y)$ permits upper calibration, while exact recovery from the current observation requires $L_o(y)=U_o(y)$. Proposition 38.3 separates these two conditions inside one fixed window. Further queries can close this gap when a complete finite probe envelope is available; merely processing the unchanged record cannot separate its unequal target values.

The bounds are local to the supplied information and need not share any global constant. The target remains the number of distinct prime divisors. None of the decoding conclusions recovers prime exponents, the hidden integer, or its generating label; any such recovery requires its own identifiability argument under the chosen source promise. Numerical overlap of windows is handled by the labeled source (38.1), not by postulating a function assigning a unique index to every $n\in W$. The adaptive impossibility applies only while the information consists of an index-side value with infinite compatible index set and finite divisibility answers. Magnitude or support promises change the compatible sources and must be included before invoking it. No claim about arbitrary arithmetic predicates, efficient factorization, or uniform calibration on all of $W$ follows.

## 追加锚（本行以下为增补区）

## 39. Finite-valued advice and persistent obstruction to adaptive upper calibration

**Definition 39.1 (Advice, probe cylinders and persistent unboundedness).** Retain exactly the labeled source $X$, numerical map $N$ and target $\Omega$ of (38.1). For finite $S\subset\mathbb P$ and a realized pattern $b\in d_S(N[X])$, write

$$
C(S,b)=\{x\in X:d_S(N(x))=b\}.
$$

Theorem 37.2 and Corollary 37.3, pulled back along the surjection $N:X\to W$, give

$$
\sup_{x\in C(S,b)}\Omega(x)=+\infty.
\tag{39.1}
$$

In fact every $b\in\{0,1\}^{S}$ is realized. This is unboundedness across the window union in (38.1).

Let $\beta:X\to E$ be any supplied side observation with finite attained range $E_0=\beta[X]$. Only $E_0$ must be finite; the ambient set $E$ need not be. No computability, continuity, measurability or index-only condition is imposed on $\beta$. For $x\in X$ and finite $T\subset\mathbb P$, define

$$
\begin{aligned}
J_\beta(x,T)
&=\{y\in X:\beta(y)=\beta(x),\ d_T(N(y))=d_T(N(x))\},\\
B_\beta
&=\{x\in X:\text{for every finite }T\subset\mathbb P,
\ \sup_{y\in J_\beta(x,T)}\Omega(y)=+\infty\}.
\end{aligned}
\tag{39.2}
$$

Every $J_\beta(x,T)$ contains $x$. Thus $x\notin B_\beta$ means that some finite $T$ and finite real $M$ satisfy $\Omega(y)\le M$ for every $y\in J_\beta(x,T)$. The set $B_\beta$ depends only on the supplied observation and source, not on a query procedure.

**Theorem 39.2 (Unbounded persistent sources in every probe cylinder).** For every $\beta$ as in Definition 39.1, every finite $S\subset\mathbb P$, every realized $b\in d_S(N[X])$, and every finite real threshold $K$, there exists

$$
x\in C(S,b)\cap B_\beta
\quad\text{with}\quad \Omega(x)>K.
\tag{39.3}
$$

**Proof.** Fix $S,b,K$ and suppose, to the contrary, that every $x\in C(S,b)$ with $\Omega(x)>K$ lies outside $B_\beta$. Put $m=|E_0|\ge1$. We construct nonempty finite probe cylinders $D_j$, sets $A_j\subseteq E_0$ of $j$ distinct advice values, and finite real bounds $H_j\ge K$, for $0\le j\le m$, satisfying

$$
D_j\subseteq C(S,b),\qquad
\Omega(y)\le H_j
\quad\text{whenever }y\in D_j\text{ and }\beta(y)\in A_j.
\tag{39.4}
$$

Start with $D_0=C(S,b)$, $A_0=\varnothing$ and $H_0=\max\{K,0\}$. Suppose the data are constructed for $j<m$, and write $D_j=C(S_j,b_j)$. By (39.1), choose $x_j\in D_j$ with $\Omega(x_j)>H_j$. Its advice value $e_j=\beta(x_j)$ is not in $A_j$, by (39.4). Since $\Omega(x_j)>K$ and $D_j\subseteq C(S,b)$, the contrary assumption gives $x_j\notin B_\beta$. Hence there are a finite prime set $T_j$ and a finite real $M_j$ such that

$$
\Omega(y)\le M_j\qquad(y\in J_\beta(x_j,T_j)).
\tag{39.5}
$$

Set

$$
\begin{aligned}
D_{j+1}
&=D_j\cap C(T_j,d_{T_j}(N(x_j)))\\
&=C(S_j\cup T_j,d_{S_j\cup T_j}(N(x_j))),\\
A_{j+1}&=A_j\cup\{e_j\},\qquad
H_{j+1}=\max\{H_j,M_j\}.
\end{aligned}
\tag{39.6}
$$

The equality of cylinders holds because $x_j\in D_j$, so the two patterns agree on their overlap. This cylinder contains $x_j$ and is again a nonempty finite probe cylinder. The bounds for advice values in $A_j$ persist under restriction to $D_{j+1}$; the bound for $e_j$ follows from (39.5), since its sources in $D_{j+1}$ belong to $J_\beta(x_j,T_j)$. Thus (39.4) holds at $j+1$, with one additional distinct advice value.

After $m$ steps, $A_m=E_0$. Equation (39.4) therefore bounds $\Omega$ by the finite number $H_m$ on all of $D_m$. This contradicts (39.1) for the nonempty cylinder $D_m$, proving (39.3).

The finite induction removes an advice value from the possible values of sources above the current bound; it does not remove all sources of that value. No regularity of the advice cells is used. The integer $m$ counts this proof's restrictions, not the number of queries made by a procedure or an effective method for selecting witnesses. In contrast with Proposition 38.5, which selects an unbounded advice cell separately for each fixed probe menu, (39.3) selects one actual $x$ before quantifying over every finite further menu $T$ in (39.2).

The finite-partition viewpoint for discrete advice and discontinuity obstructions is established background; see Martin Ziegler, *Real Computation with Least Discrete Advice: A Complexity Theory of Nonuniform Computability*, [arXiv:0811.3782v5, Sections 1.2 and 2.1](https://arxiv.org/html/0811.3782v5), [doi:10.1016/j.apal.2011.12.030](https://doi.org/10.1016/j.apal.2011.12.030). The argument above uses the elementary finite-color elimination principle directly on the cylinders (39.1). It does not apply a represented-space or Cauchy-representation theorem to $X$. The source-specific conclusion (39.3) is a deduction from the every-pattern unboundedness supplied by Theorem 37.2 and Corollary 37.3; no literature-priority claim is made.

**Corollary 39.3 (No total finite upper certification with finite-valued advice).** Let $\beta$ satisfy Definition 39.1. Consider a deterministic procedure on an unknown $x\in X$ whose source information consists only of $\beta(x)$ and answers to queries $p\mid N(x)$ for primes $p$. The next query, stopping decision and output may depend on the advice, the preceding query-answer transcript and fixed parameters common to all of $X$. A successful halt occurs after finite execution and outputs a finite real number $c$ as an upper certificate. Soundness means that every such output on every $x\in X$ satisfies $\Omega(x)\le c$; successful halting is not assumed.

Every sound procedure of this kind has no successful halt on any $x\in B_\beta$. In particular, no such procedure is total in the sense of successfully halting with a finite upper certificate on every source. Each finite cylinder $C(S,b)$ contains noncertifying sources with unbounded $\Omega$, and the same set $B_\beta$ obstructs every such sound procedure. No uniform bound on query depth is assumed. If every allowed halt must output a finite upper certificate, every run on $B_\beta$ genuinely fails to halt. If other halt outcomes are allowed, abort, unknown and $+\infty$ are not finite upper certificates.

**Proof.** Suppose a sound procedure successfully halts at $x\in B_\beta$. Deduplicate the primes in its finite realized transcript into $T$; repeated answers are consistent. Every $y\in J_\beta(x,T)$ has the same initial advice and follows the same entire finite execution. Indeed, at the start both runs have the same fixed parameters and advice. Inductively, the same earlier transcript gives the same next query or stopping decision, and membership in $J_\beta(x,T)$ gives the same answer to each prime on the path. Thus every such $y$ reaches the same successful halt and finite output $c$. This is the deterministic transcript argument of Theorem 37.6 with the advice held fixed; it includes a transcript of length zero.

Soundness then gives $\Omega(y)\le c$ for all $y\in J_\beta(x,T)$, contradicting (39.2). Theorem 39.2 supplies sources in $B_\beta$ of arbitrarily large $\Omega$ in every $C(S,b)$, which proves the remaining assertions. The finite set $T$ was extracted from the single hypothesized successful run, so it can depend on that source and that procedure.

In the calibration language of (38.2), for $o_{\beta,T}(y)=(\beta(y),d_T(N(y)))$ and every $x\in B_\beta$, the upper endpoint obeys

$$
U_{o_{\beta,T}}(o_{\beta,T}(x))=+\infty
\qquad\text{for every finite }T\subset\mathbb P.
\tag{39.7}
$$

Thus no finite stage along such an actual source provides a finite upper calibration, even if the stage and probes depend on its earlier answers. For any fixed $S,b$, subtracting the constant observed contribution yields the further source-specific consequence

$$
\sup_{x\in C(S,b)\cap B_\beta}\rho_S(N(x))=+\infty.
\tag{39.8}
$$

To see this for any finite threshold $H$, apply (39.3) with $K=H+\sum_{p\in S}b_p$ and use $\rho_S(N(x))=\Omega(x)-\sum_{p\in S}b_p$. The sufficient index, magnitude and complete-support promises of Proposition 38.4 remain applicable on their declared domains. Such promises change the compatible sources; (39.7) does not turn a bounded individual advice cell into an unbounded one.

The finite-path argument is standard decision-tree reasoning; compare the deterministic query-tree background in [Magniez, Nayak, Santha, Sherman, Tardos and Xiao, *Improved bounds for the randomized decision tree complexity of recursive majority*, p. 2](https://arxiv.org/abs/1309.7565v1), as recorded in [the existing source note](../../../Library/ConceptDynamics/magniez2013randomized.md). Finite-domain depth bounds from that setting are not used here. The conclusion concerns deterministic prime-divisibility queries on (38.1); it gives neither an obstruction for arbitrary predicates or randomized protocols nor a factoring-complexity, efficient witness-selection or physical-resource bound. Every individual window is finite; (39.3) and (39.8) range over the window union.

**Proposition 39.4 (Bounded cells, partial success and the finite-range boundary).** On the same source $X$, define the two-valued observation

$$
\beta_1(x)=
\begin{cases}
0,&\Omega(x)\le1,\\
1,&\Omega(x)>1.
\end{cases}
\tag{39.9}
$$

Both cells are occupied, the zero cell is bounded, and

$$
B_{\beta_1}=\{x\in X:\Omega(x)>1\}.
\tag{39.10}
$$

A sound partial procedure may successfully output $1$ without prime queries on the zero cell and make no successful output on the one cell. In contrast, allowing advice that is a finite string at each source with infinitely many possible strings permits a sound total procedure with no prime queries: take $\gamma(x)=1^{\Omega(x)}$ and output its length.

**Proof.** Proposition 37.5 supplies the labeled sources $(7,2)$ and $(13,26)$ with target values $1$ and $2$, so both cells in (39.9) are occupied. If $\beta_1(x)=0$, every $J_{\beta_1}(x,T)$ has target at most $1$, and $x\notin B_{\beta_1}$. If $\beta_1(x)=1$, fix any finite $T$. The cylinder $C(T,d_T(N(x)))$ has unbounded target by (39.1). Removing its sources with target at most $1$ leaves an unbounded set, exactly $J_{\beta_1}(x,T)$. Explicitly, for any finite $H$, choose in the cylinder a source with target greater than $\max\{1,H\}$; it belongs to that joint cell. This proves (39.10).

The stated partial procedure is sound by the definition of the zero cell; on the one cell it may run forever. Replacing this nonhalting branch by unknown gives a procedure that halts everywhere but is still not total finite upper certification. This refutes both the assertion that every cell of every finite-valued observation must be unbounded and the assertion that no source can admit sound partial certification with such advice.

Finally, every $\Omega(x)$ is a finite integer, so $\gamma(x)$ is a finite word over the one-letter alphabet and its length is exactly the target. Equation (39.1) for $S=\varnothing$ makes these lengths unbounded, hence the attained range of $\gamma$ is infinite. Reading the supplied word and returning its length terminates at each source, but the finite-range hypothesis of Theorem 39.2 fails. This is a distinction between finite attained range and pointwise finite strings of unbounded possible lengths, not a way to obtain the advice from the prime-query transcript.

## 追加锚（本行以下为增补区）

## 40. Randomized upper proposals under a uniform error budget

**Definition 40.1 (Common tapes and the finite upper-output task).** Retain exactly $X,N,\Omega$ from (38.1), and $\beta:X\to E$, its finite attained range $E_0$, $J_\beta$ and $B_\beta$ from Definition 39.1. Fix one probability space $(\Theta,\mathcal F,\mu)$ common to every source. A tape $\theta\in\Theta$ fixes a deterministic procedure whose only source inputs are $\beta(x)$ and Boolean answers to prime-divisibility queries $p\mid N(x)$. Its next action, stopping decision and output depend only on that tape, the advice, its preceding execution and fixed parameters shared by all sources. No distribution on $X$ is imposed; source independence means that the tape law and these rules are the same for every fixed $x$.

For each $x$, let $L_x\subseteq\Theta$ be the event of literal termination after finite execution, and let $H_x\subseteq L_x$ be the event that this termination outputs a finite real number $C_x(\theta)$ as a proposed upper bound. A finite proposal may be correct or false. Other terminal outcomes, including unknown, abort and $+\infty$, belong to $L_x\setminus H_x$. There is one terminal outcome per run; intermediate numerical values are not upper outputs. On $H_x$, write $\tau_x(\theta)\in\mathbb N_0$ for its finite execution length and $Q_x(\theta)$ for the finite set of primes queried on that execution, including the empty set when no query occurs.

Measurability is part of the contract: for every fixed $x$, all finite execution records and terminal outcomes are measurable in $\theta$, with discrete query, answer and status fields and Borel real-output fields. In particular $L_x,H_x\in\mathcal F$, and the restricted maps $\tau_x$, $Q_x$ and $C_x$ on $H_x$ are measurable, where finite prime sets carry their countable discrete sigma algebra. Thus the truncation events below and the false-output event are measurable. No regularity of $\beta$ on $X$ is required. Define

$$
\begin{aligned}
F_x&=\{\theta\in H_x:C_x(\theta)<\Omega(x)\},&
S_x&=H_x\setminus F_x,\\
U_x&=\Theta\setminus H_x,&
D_x&=\Theta\setminus L_x.
\end{aligned}
\tag{40.1}
$$

Here $S_x$ is finite successful output, meaning correctness at the actual source; it does not assert soundness on the whole observation cell. $U_x$ is operational uncertainty for this task: no finite upper proposal is returned. It includes unknown/abort and infinite outputs as well as literal nontermination $D_x$. It is neither posterior uncertainty nor the event of an incorrect proposal. The latter is $F_x$; failure to obtain a correct finite output is $U_x\cup F_x=\Theta\setminus S_x$.

The common-tape convention follows the distribution-over-deterministic-procedures convention in [Magniez et al., *Improved bounds for the randomized decision tree complexity of recursive majority*, p. 2](https://arxiv.org/pdf/1309.7565v1), also recorded in [the existing source note](../../../Library/ConceptDynamics/magniez2013randomized.md). Its finite Boolean input domain and depth bounds are not hypotheses here. The distinction between one input-independent law, sourcewise probabilistic correctness and every-tape correctness is already present in [ExactRealProbeCosts](../../../D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts.lean); those exact-real probes do not replace the prime queries in this definition.

**Theorem 40.2 (Uniform false-output control bounds finite output on $B_\beta$).** For every procedure satisfying Definition 40.1 and every common $\delta\in[0,1]$, suppose

$$
\mu(F_y)\le\delta\qquad\text{for every }y\in X.
\tag{40.2}
$$

Then, for every $x\in B_\beta$,

$$
\mu(H_x)\le\delta,\qquad
\mu(U_x)\ge1-\delta,\qquad
\mu(S_x)\le\delta-\mu(F_x)\le\delta.
\tag{40.3}
$$

There is no uniform query-depth or execution-horizon assumption. At $\delta=0$, (40.3) asserts almost-sure absence of finite output at each obstructed source, without asserting absence on every declared tape. In particular, for $\delta<1$ no such procedure returns a finite upper proposal almost surely at every source. The obstructing set is the same procedure-independent $B_\beta$ as in Section 39, which has unbounded target in every finite probe cylinder by Theorem 39.2.

**Proof.** Fix $x\in B_\beta$. Enumerate all primes increasingly as $p_1,p_2,\ldots$ and put $P_m=\{p_1,\ldots,p_m\}$ for $m\ge1$. On the common tape space define

$$
A_m=\{\theta\in H_x:\tau_x(\theta)\le m,\ Q_x(\theta)\subseteq P_m,\ C_x(\theta)\le m\}.
\tag{40.4}
$$

These are measurable increasing events and $\bigcup_{m\ge1}A_m=H_x$: each execution producing a finite proposal has finite length, finitely many queried primes and a finite real output. This exhaustion does not bound these quantities uniformly over tapes or sources.

For each $m$, persistent unboundedness gives one source

$$
y_m\in J_\beta(x,P_m),\qquad \Omega(y_m)>m.
\tag{40.5}
$$

This $y_m$ depends on $x,m$ but not on the tape. For every $\theta\in A_m$, run both sources with that very same tape. They have the same advice, and every prime queried along the run at $x$ lies in $P_m$, on which their answers agree. The deterministic finite-execution transport used in Corollary 39.3 therefore makes the run at $y_m$ terminate with exactly $C_x(\theta)\le m<\Omega(y_m)$. This is the same-history transport of [PassivePolicyNormalization, `execute_transfer`](../../../D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization.lean), with tape and advice fixed; no new generic transport assertion is needed. Consequently

$$
A_m\subseteq F_{y_m},\qquad
\mu(A_m)\le\mu(F_{y_m})\le\delta.
\tag{40.6}
$$

Continuity from below now yields $\mu(H_x)=\lim_m\mu(A_m)\le\delta$. Taking complements and using $H_x=S_x\sqcup F_x$ proves (40.3). The proof selects one actual source for the entire event $A_m$, not a different source for each tape. Both inclusion and probability comparison use the common law $\mu$; merely finding a bad source separately for each tape would not establish (40.6).

The source-specific probability bridge is a `repo-derived` deduction from persistent unboundedness and finite-path transport, with ordinary probability continuity. The every-pattern arithmetic supplier remains Theorem 37.2 through Sections 36–39. No Lean/kernel verification or literature priority is claimed. Established confidence-impossibility background includes the Gleser–Hwang theorem as presented by [Moss, *Infinite Diameter Confidence Sets in Hedges' Publication Bias Model*, Theorem 4](https://arxiv.org/pdf/1912.09180v3), and [Bertanha–Moreira, *Impossible Inference in Econometrics: Theory and Applications*, Theorem 3](https://arxiv.org/pdf/1612.02024v5). Moss assumes pointwise convergence of dominated densities to a density, support inclusion and diverging parameter size; Bertanha–Moreira use a common weak limit of convex mixtures from each parameter class and specified boundary-continuity conditions. Those hypotheses are not imported here. These results provide context; (40.4)–(40.6) supply the prime-query argument.

**Proposition 40.3 (Sharpness, coverage and termination).** Write $h_x=\mu(H_x)$, $e_x=\mu(F_x)$ and $s_x=\mu(S_x)$. Under (40.2), at every $x\in B_\beta$,

$$
0\le s_x=h_x-e_x\le\delta-e_x,\qquad
\mu(\Theta\setminus S_x)=1-h_x+e_x\ge1-\delta+e_x.
\tag{40.7}
$$

When $h_x>0$, coverage conditional on a finite proposal is

$$
\mu(S_x\mid H_x)=1-\frac{e_x}{h_x}.
\tag{40.8}
$$

The unconditional error guarantee $e_x\le\delta$ alone does not give conditional coverage $1-\delta$. The bound $h_x\le\delta$ is sharp; for $0<\delta<1$, conditional coverage can be either zero or one within the same admissible procedure. Moreover (40.3) gives no lower bound $1-\delta$ on literal nontermination unless every allowed terminal outcome is a finite upper proposal.

**Proof.** Equations (40.7)–(40.8) follow from the disjoint decomposition $H_x=S_x\sqcup F_x$. For the assertions of attainability, take constant $\beta$, so $B_\beta=X$ by (39.1). Use a Bernoulli tape of success probability $\delta$: on success output the upper proposal $1$ without queries, and otherwise halt with unknown. Then for every $x$,

$$
h_x=\delta,\qquad
e_x=\delta\,\mathbf1_{\{\Omega(x)>1\}},\qquad
s_x=\delta\,\mathbf1_{\{\Omega(x)\le1\}},\qquad
\mu(D_x)=0.
\tag{40.9}
$$

The labeled sources $(7,2)$ and $(13,26)$ have target values $1$ and $2$, respectively, as supplied by Proposition 39.4. For $\delta>0$ their conditional coverages are one and zero. Thus all probabilities in (40.9) meet the common error budget, attain $h_x=\delta$, and separate conditional coverage from unconditional successful-output probability. For $\delta=0$ the finite-proposal probability is zero and conditional coverage is undefined. If every halt must instead be a finite upper proposal, then $L_x=H_x$, hence $D_x=U_x$ and (40.3) does yield $\mu(D_x)\ge1-\delta$.

**Proposition 40.4 (Pointwise budgets without a common gap from one).** Replacing the single bound $\delta<1$ by merely a source-dependent bound $\delta_x<1$ does not preclude finite upper output with probability one, even with constant advice and no queries.

**Proof.** On the same source $X$, draw an integer $K\ge1$ from the source-independent law $\mu(K=k)=2^{-k}$ and immediately output $K$. Every tape in this discrete probability space gives a finite output. For $m=\Omega(x)\ge1$, the geometric sum gives

$$
h_x=1,\qquad
e_x=\mu(K<m)=1-2^{-(m-1)}<1,\qquad
s_x=2^{-(m-1)}>0.
\tag{40.10}
$$

Here $\Omega(x)\ge1$ because every source has $N(x)>1$. Taking $\delta_x=e_x$ proves the assertion. Unboundedness of $\Omega$ gives $\sup_x\delta_x=1$, so this example supplies no common budget smaller than one and does not contradict Theorem 40.2. A source-dependent budget with a common upper bound below one is still covered by that theorem.

The calibration meaning of Theorem 40.2 is task-relative: on the intrinsic obstruction $B_\beta$, uniformly limiting false finite upper proposals to $\delta$ also limits the probability of obtaining any finite proposal to $\delta$. Randomization alone leaves at least $1-\delta$ probability without such a proposal; counting actual incorrect proposals as unresolved increases the failure probability as in (40.7). The local upper endpoint (39.7) remains infinite at each finite prime transcript. The claim does not rule out bounded advice cells or the explicit index, magnitude and complete-support promises of Proposition 38.4. Source-correlated random tapes, hidden source inputs and arbitrary non-prime probes fall outside Definition 40.1; no factoring-efficiency, uniform resource or physical conclusion follows.

## 追加锚（本行以下为增补区）

## 41. Output-conditioned error and the literal-divergence tradeoff

**Definition 41.1 (Uniform conditional error).** Retain the source, advice, common tape, finite records and events of Definition 40.1. Fix one $\delta\in[0,1]$ and replace (40.2) by

$$
e_y\le\delta h_y\qquad(y\in X).
\tag{41.1}
$$

Here $h_y=\mu(H_y)$ and $e_y=\mu(F_y)$. This is the sourcewise conditional false-output bound $\mu(F_y\mid H_y)\le\delta$ whenever $h_y>0$, with the zero-proposal case read as $e_y=0$ and no conditional probability assigned. Put $d_y=\mu(D_y)$ for literal nontermination. Unknown, abort and $+\infty$ remain finite terminal outcomes outside $H_y$ and are not counted as $D_y$. Conditioning an error guarantee on selection is standard; see [Fithian, Sun and Taylor, *Optimal Inference After Model Selection*, arXiv:1410.2597v4, §§2.2 and 2.4, equations (9) and (14)](https://arxiv.org/html/1410.2597v4). Here the selected event is finite output in Definition 40.1; no statistical sampling model from that reference is assumed.

**Corollary 41.2 (Persistent sources force a proposal--divergence tradeoff).** Under Definition 41.1, every $x\in B_\beta$ satisfies

$$
(1-\delta)h_x\le\delta d_x.
\tag{41.2}
$$

Equivalently, for $0<\delta<1$, $d_x\ge(1-\delta)h_x/\delta$. At $\delta=0$ one has $h_x=0$; at $\delta=1$ the inequality is the tautology $0\le d_x$.

**Proof.** Reuse Theorem 40.2 on the product tape space $(\Theta^{\mathbb N},\mathcal F^{\otimes\mathbb N},\mu^{\otimes\mathbb N})$. Run the original procedure on a fresh coordinate, retain a finite proposal, and restart after every finite terminal record outside $H_y$; a coordinate in $D_y$ leaves the restarted run divergent. Each restart is an execution transition. Infinitely many immediate unknown outcomes therefore constitute an infinite execution, not a finite output. The product law and restart rule are common to all sources.

Put $R_y=L_y\setminus H_y$ and $r_y=\mu(R_y)=1-h_y-d_y$. Proposal on attempt $n\ge1$ is the cylinder $R_y^{n-1}\times H_y\times\Theta^{\mathbb N}$, with false-output counterpart obtained by replacing $H_y$ by $F_y$. These events are disjoint across $n$ and have probabilities $r_y^{n-1}h_y$ and $r_y^{n-1}e_y$. Summing gives

$$
\widetilde h_y=\frac{h_y}{h_y+d_y},\qquad
\widetilde e_y=\frac{e_y}{h_y+d_y}
\tag{41.3}
$$

when $h_y+d_y>0$, and both are $0$ otherwise: in the latter case $h_y=e_y=0$, so every term of both sums is zero. Each finite restarted record comprises finitely many finite executions and restart transitions. Its events, including Borel restrictions on the final real output, are measurable by Definition 40.1 and countable unions over attempt counts and discrete finite histories. No countability of real outputs or uniform horizon is needed. Equation (41.1) gives $\widetilde e_y\le\delta h_y/(h_y+d_y)\le\delta$ when the denominator is positive, and the zero case also satisfies this bound.

Explicitly, use (40.4) for the restarted procedure: the event $\widetilde A_m$ bounds its total execution length by $m$, all queried primes by $P_m=\{p_1,\ldots,p_m\}$, and its final output by $m$. For $x\in B_\beta$, choose one actual $y_m\in J_\beta(x,P_m)$ with $\Omega(y_m)>m$ before quantifying over tapes. Every tape in $\widetilde A_m$ follows the same complete execution at $y_m$, including all failed attempts and restart transitions; all its prime answers agree. Thus the whole event lies in $\widetilde F_{y_m}$ and has product measure at most $\delta$. Overlapping menus and repeated queries use this same source and tape. These increasing events exhaust $\widetilde H_x$, so $\widetilde h_x\le\delta$ by continuity from below, exactly as in Theorem 40.2. Multiplying (41.3) by $h_x+d_x>0$ proves (41.2); if this denominator is zero, both sides of (41.2) are zero. The endpoint conclusions follow directly. $\square$

**Proposition 41.3 (Attainment at a persistent arithmetic source).** There is a supplied numerical advice map $\beta_*:X\to\{0,1\}$ with both values attained, independent of $\delta$, such that $x_*=(7,2)\in B_{\beta_*}$. For every $\delta\in[0,1]$ there is one procedure satisfying Definition 41.1 on all of the unchanged $X$, with $h_{x_*}=\delta$, $e_{x_*}=0$ and $d_{x_*}=1-\delta$. Its deterministic parameters have a finite description, and every individual search used to generate them terminates.

**Proof.** The arithmetic supplier is Theorem 37.2, with the labeled source of (38.1). Proposition 37.5 gives $F_7=13$, $I_7=\{2\}$ and $N(x_*)=27=3^3$, hence $\Omega(x_*)=1$. For an integer $M\ge2$, put $P(M)=\{p\in\mathbb P:p\le M\}$. Define $n_0=27$. Inductively enumerate prime indices $r$ increasingly and, for each $r$, the finite set $I_r$ increasingly. Select the first labeled source $z_j=(r_j,g_j)$ whose value $n_j=N(z_j)$ satisfies

$$
S_j=P(n_{j-1}),\qquad d_{S_j}(n_j)=d_{S_j}(27),\qquad
\rho_{S_j}(n_j)\ge j\qquad(j\ge1).
\tag{41.4}
$$

Theorem 37.2 supplies such a source for every finite $S_j$ and integer $j\ge1$. The enumeration reaches any given source after finitely many candidates; the Fibonacci recurrence, finite prime tests and trial division decide each candidate condition in finite time. Thus the first selection terminates, and induction proves termination of every individual selection. This is one fixed construction on $X$, with no access to the unknown source of a later run.

Since $3\in S_j$, equation (41.4) gives $3\mid n_j$ and no other divisor in $S_j$. At least one prime outside $S_j$ divides $n_j$, so $n_j>n_{j-1}$. Put $c_j=\omega(n_j)\ge j+1$ and let $q_j$ be the least prime divisor of $n_j$ other than $3$; finite trial division computes both. Then

$$
q_j>n_{j-1},\qquad q_j\nmid27,\qquad
q_j\mid n_i\ \Longleftrightarrow\ i=j\qquad(i,j\ge1).
\tag{41.5}
$$

Indeed, for $i<j$ one has $n_i\le n_{j-1}<q_j$. For $i>j$, the set $S_i$ contains $q_j\le n_j\le n_{i-1}$, and (41.4) forces its bit to be that of $27$, namely zero. The case $i=j$ holds by definition. This also shows that the primes $q_j$ are distinct.

Define the numerical set and its pulled-back advice by

$$
V=\{27\}\cup\{n_j:j\ge1\},\qquad
\beta_*(y)=\begin{cases}0,&N(y)\in V,\\1,&N(y)\notin V.\end{cases}
\tag{41.6}
$$

All labels with the same numerical value have the same advice. Both values occur: $x_*$ has value zero, while $(5,1)\in X$ has $N(5,1)=6$ and value one, since every $n_j$ is odd by its bit at $2\in S_j$. Membership in $V$, if the integer itself is supplied, is decidable by generating the strictly increasing unbounded sequence until it reaches or passes that integer (and separately checking $27$). Each stage terminates by the preceding argument. The query procedure below receives only the supplied advice, not that integer or its label; this decidability statement does not supply an acquisition operation for advice.

To prove persistence, fix any finite prime menu $T$ and any finite real $K$. Since $n_j$ is strictly increasing, choose $j$ with $T\subseteq P(n_{j-1})$ and $j+1>K$; the empty menu imposes no first restriction. The single actual source $z_j$ then satisfies

$$
\beta_*(z_j)=\beta_*(x_*)=0,\qquad
d_T(N(z_j))=d_T(27),\qquad \Omega(z_j)=c_j\ge j+1>K.
\tag{41.7}
$$

This proves $x_*\in B_{\beta_*}$ by (39.2). The argument works also for the union of any finitely many finite menus, so their shared coordinates and overlaps are realized simultaneously. Numerical duplicates of $27$ or $n_j$ in other windows change neither advice, target nor any prime answer. In contrast, within advice zero the positive answer at $q_j$ identifies the numerical value $n_j$ by (41.5), even when its generating label is not unique.

For fixed $\delta$, take the common tape space $\Theta=\{0,1\}$ with its full sigma algebra and law $\mu(\{1\})=\delta$, $\mu(\{0\})=1-\delta$. On advice one, halt with unknown. On advice zero and tape one, output the finite proposal $1$. On advice zero and tape zero, generate $(q_j,c_j)$ in order, query each $q_j\mid N(y)$, and at the first positive answer output $c_j$; otherwise continue to the next index. These are the entire rules for every source. All generation steps use the same fixed arithmetic searches, and every source observation in this branch is the stated prime query.

At $N(y)=27$, tape zero receives only negative answers and makes infinitely many queries, hence literally never terminates; tape one gives the correct output $1$. At $N(y)=n_j$, tape zero reaches its first positive answer exactly at $q_j$ after finitely many terminating searches and queries, and returns $c_j=\Omega(y)$; tape one returns the false proposal $1<c_j$. Every remaining source has advice one and terminates with unknown. Therefore the complete probability rows for this one procedure are

| Source class | $h_y$ | $e_y$ | $d_y$ | $\mu(L_y\setminus H_y)$ |
| --- | --- | --- | --- | --- |
| $N(y)=27$ | $\delta$ | $0$ | $1-\delta$ | $0$ |
| $N(y)=n_j$ for some $j\ge1$ | $1$ | $\delta$ | $0$ | $0$ |
| $N(y)\notin V$ | $0$ | $0$ | $0$ | $1$ |

Every finite record and terminal restriction is measurable on this two-point tape space. The rows exhaust $X$ and show $e_y\le\delta h_y$ everywhere, including every zero denominator. At $x_*$ they give

$$
(h_{x_*},e_{x_*},d_{x_*})=(\delta,0,1-\delta),\qquad
(1-\delta)h_{x_*}=\delta d_{x_*}=\delta(1-\delta).
\tag{41.8}
$$

The endpoint laws $\delta=0,1$ give respectively $(0,0,1)$ and $(1,0,0)$ at $x_*$. Conditional error is asserted only when $h_y>0$; (41.1) itself holds at both endpoints. The Bernoulli law is stipulated for each real $\delta$ and is independent of the source; no effective exact sampler for an arbitrary real parameter is assumed. The arithmetic generation has a finite description with pointwise terminating searches, without a uniform bound on search time or query length. All uses of $V$ are through the supplied numerical advice, and all further source access consists of prime queries. $\square$

## 追加锚（本行以下为增补区）

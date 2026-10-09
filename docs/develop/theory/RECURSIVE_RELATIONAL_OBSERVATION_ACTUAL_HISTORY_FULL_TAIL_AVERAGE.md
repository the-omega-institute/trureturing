# Actual-history averages of complete stopped residual laws

## 1. Original source, actual weights and observer classes

**Mathematical status.** This volume gives an ordinary mathematical proof. It is reference input, has no Lean kernel verification, and makes no kernel or freezing claim.

**Convention 1.1 (unchanged source and full residual target).** Use exactly [PC, Definitions 1.2–1.5][PC]: $m=2,d=1,\ell=2,n=4$, and a fixed finite or countable probability prior $\mu$ on positive integer depths with $\mu(1),\mu(2)>0$. Before the first paid Read, draw one actual $K\sim\mu$. Conditional on that same $K=k$, all legal restored Reads are fresh independent letters, with

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad \frac13\le r_k\le\frac25.
\tag{1.1}
$$

The original seed parser pays for every rejected equal pair; $\alpha\beta$ acquires seed0 and $\beta\alpha$ acquires seed1. The four payload stages, their return circles, original bare fields and selector, full-marker-tree $B,Q^+,Z$ writer, third-write-before-latch, record holding, fourth completion and unique original $\mathrm{Stop}_b$ all remain as supplied. Both seeds, every marker triple and every finite rejection or return history belong to the domain. Pending and delivered states have no Read permission. There is no conditioning on future $E_1$, source reset, extra probe or source cutoff. The full-tree writer in [E1, §2][E1] supplies record updates on all original marker prefixes; its six-cell recovery theorem is not used to restrict this prediction domain.

Write $c=C_0(h)$ for the complete original finite control and record configuration, and $\mathcal H_3$ for the original third-latch histories, before any fourth-stage Read. At each such history the target $T_h^\mu$ is the complete residual transcript law: current $c$, all future Read letters and their original control, record, completion and Stop events, in their original order. Original infinite noncompletion paths remain in the sample space. Given $c$, the letters determine the derived events and are recoverable from the transcript; thus the supplied map $I_c$ is injective. Neither the terminal outcome nor a finite future horizon replaces this target.

Let $A(h),B(h)$ count every actually acquired $\alpha,\beta$, including rejected seed letters. For nonnegative integers $a,b$, put

$$
Z_\mu(a,b)=\sum_k\mu(k)r_k^a(1-r_k)^b,
\qquad
\lambda_\mu(a,b)=\frac{Z_\mu(a+1,b)}{Z_\mu(a,b)}.
\tag{1.2}
$$

The likelihood and same-source stopping bridge are supplied by [FR, §§9,15][FR] and [BD, §§97.1,100.1][BD]. In particular $Z_\mu(a,b)>0$, $\lambda_\mu(a,b)\in[1/3,2/5]$, and the latter is the actual next-$\alpha$ probability on any active history with those acquired counts. These are analytic coordinates, not additional observer inputs.

Let $T_3,T_4$ be the actual total paid Read counts through the third and fourth marker completions. Stop adds no Read. The countable stopping set $\mathcal H_3$ is prefix-free, and its actual weights are

$$
p_\mu(h)=\Pr_\mu(H_3=h)=Z_\mu(A(h),B(h))>0,
\qquad \sum_{h\in\mathcal H_3}p_\mu(h)=1.
\tag{1.3}
$$

Indeed, specifying one legal stopped letter prefix specifies the history; deterministic parsing and recording add no likelihood factor. Almost-sure seed and marker completion are supplied by [BD, Propositions 97.2,100.2][BD]. For the same actual $K$, equation (100.4) there gives

$$
\begin{aligned}
\mathbb E_\mu T_4
&=\sum_k\mu(k)\left[\frac1{r_k(1-r_k)}
       +\frac{4(2-r_k)}{1-r_k+r_k^2}\right]\le C,\\
C&=\frac92+\frac{60}7=\frac{183}{14},
\qquad \Pr_\mu(T_4>N)\le\frac C N\quad(N\ge1).
\end{aligned}
\tag{1.4}
$$

This uses the original outer mixture over one $K$, with nonnegative summation and expectation additivity. It does not assert independence of the separately mixed stages, require a depth moment, or provide a finite worst-case Read bound.

**Definition 1.2 (the two actual-average risks).** Let $\mathcal F_{\rm coh}$ be the original finite complete observer class of [PC, Definition 1.4][PC], restricted by both conditions in its Definition 1.5 on their whole original legal domain: per-configuration generation by the same letter update, and actual-history marginalized update compatibility. Initialization precedes the first paid Read and is independent of the realized source. No fixed finite size budget is imposed. Let $\mathcal F_{\rm det}\subset\mathcal F_{\rm coh}$ be its deterministic-retention subclass. With the original conditional configuration distribution $\rho_h$ and normalized full-law decoder $D_z$, define

$$
\begin{aligned}
\overline D_h^O&=\sum_z\rho_h(z)D_z,\\
e_{\rm law}^O(h)&=\operatorname{TV}(\overline D_h^O,T_h^\mu),\\
e_{\rm conf}^O(h)&=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),\\
\mathcal A_j^\mu(O)&=\sum_{h\in\mathcal H_3}p_\mu(h)e_j^O(h),
\qquad j\in\{\mathrm{law},\mathrm{conf}\}.
\end{aligned}
\tag{1.5}
$$

TV is half the $\ell^1$ distance. Observer randomness remains in these two different orders; $\rho_h$ is not a runtime decoder input. Convexity gives $e_{\rm law}\le e_{\rm conf}$ and $\mathcal A_{\rm law}\le\mathcal A_{\rm conf}$. Fix $\mu$ first, choose one initialized observer, average under that same actual source, and then take the infimum over observers. This is neither a per-history observer choice nor an average over priors.

## 2. Zero infima without finite attainment

**Theorem 2.1 (all admitted priors, both original risks and both compatibilities).** For every prior in Convention 1.1 and each $j\in\{\mathrm{law},\mathrm{conf}\}$,

$$
\inf_{O\in\mathcal F_{\rm coh}}\mathcal A_j^\mu(O)
=\inf_{O\in\mathcal F_{\rm det}}\mathcal A_j^\mu(O)=0.
\tag{2.1}
$$

Every individual $O\in\mathcal F_{\rm coh}$ has strictly positive values of both averages. Hence all four infima are unattained. For every fixed $\mu$ and $\varepsilon>0$, one finite deterministic observer, installed before the first actual Read, simultaneously has $\mathcal A_{\rm law}^\mu=\mathcal A_{\rm conf}^\mu<\varepsilon$. No rationality, finite-support, computability, entropy or mean-depth assumption on $\mu$ is needed for this ordinary existence statement.

Proof. We construct a complete finite generator and bound its complete-law error, then use the existing worst-history obstruction for nonattainment.

### 2.1 Finite installed rows and the unchanged actual update

Fix integers $N\ge1$ and $b\ge4$, and set $\delta=2^{-b}$. For each of the finitely many $(a,d)$ with $a+d<N$, choose an installed dyadic number $q_{a,d}$, with denominator $2^b$, such that

$$
\frac14\le q_{a,d}\le\frac12,
\qquad |q_{a,d}-\lambda_\mu(a,d)|\le\delta.
\tag{2.2}
$$

For example, $q_{a,d}=2^{-b}\lfloor2^b\lambda_\mu(a,d)\rfloor$ provides such a value, since the true row lies in $[1/3,2/5]$. The finitely many selected integers are installed data. The machine does not retain or consult $\mu$, $K$, an exact posterior or any real-valued register at runtime.

The monitor alphabet is

$$
\mathcal V_N=\{(a,d)\in\mathbb N^2:a+d<N\}\cup\{\bot\}.
\tag{2.3}
$$

Initialize $(C_{0,\mathrm{initial}},(0,0))$ before the first paid Read. On every actual Read, perform the unchanged original update $\Delta(c,x)$ and increment the corresponding monitor count if the new sum is below $N$. The Read reaching $N$ changes the monitor to permanent overflow $\bot$. Overflow holds thereafter while all original control and record updates continue. Original Stop performs its prescribed update and leaves the monitor alone. This deterministic augmented update $U$ is time-homogeneous and source-independent. Every paid seed rejection and return is counted until overflow; afterwards every such Read still executes the original process. Overflow restricts retained calibration information, not execution or the benchmark histories.

At an active nonoverflow configuration, the predictive generator chooses $\alpha$ with probability $q_{a,d}$. At overflow it uses fixed $\alpha$ probability $r_1=1/3$ at every active phase. Each synthetic letter executes that same $U$. At pending it generates precisely the original $\mathrm{Stop}_b$ and its update; at delivered it generates the empty residual. Define $D_z$ to be the full law of this generator from $z$, with current original $c$ and all original derived events included. At earlier phases it describes the remaining original stages through Stop, so generation is defined before as well as after $H_3$.

This continuation is the already supplied depth1 stopped law and original parser, not a new optimized fallback. Before overflow the generator either completes or reaches $\bot$ after finitely many Reads. A partially read seed pair resolves on the next Read. Thereafter the seed rejection probability per full pair is $5/9<1$ and the payload return probability per circle is $2/9<1$. A partial payload circle likewise completes or returns after one Read. The remaining number of stages is finite. Thus every $D_z$ is normalized, completes almost surely, and assigns zero mass to the original infinite noncompletion paths without removing them. It includes arbitrarily long finite tails; a finite horizon is never substituted.

### 2.2 Both compatibility laws on the entire legal domain

Write $s_z(x)$ for the generator's active letter row. All its active rows are strictly positive. Row products and the deterministic original events give, for every legal next letter and remaining continuation,

$$
D_z(xw)=s_z(x)D_{U(z,x)}(w).
\tag{2.4}
$$

Here $xw$ abbreviates the operation transcript, including the events determined by $\Delta$, and the right side starts with the updated original configuration after deletion of that operation prefix. Iteration gives the same factorization for every legal finite prefix. Pending Stop has probability one and the prescribed residual; delivered has no further operation. This proves per-configuration same-update generation, including seed acquisition, rejected pairs, all four payload stages, overflow and both terminal cuts.

Actual retention is deterministic: $\rho_h$ is a point mass at $z(h)$ and $z(hx)=U(z(h),x)$. Consequently $\overline D_h=D_{z(h)}$, and (2.4) separately proves actual-history marginalized update compatibility on every original legal prefix with positive predictive probability. This implication uses deterministic retention; it is not asserted for arbitrary randomized competitors. The original full-tree writer and latch order are part of $\Delta$ on every branch, independently of whether that history will satisfy $E_1$.

### 2.3 Complete-tail comparison under the actual stopping law

For $h\in\mathcal H_3$, write $t=T_3(h)=A(h)+B(h)$. When $t<N$, analytically couple the true conditional future and the predictive generator while their letters agree, until original fourth completion or total acquired count $N$. At each matched active prefix before that boundary, the monitor has the true acquired counts. Its two next-letter laws are Bernoulli rows whose parameters differ by at most $\delta$; an optimal two-letter coupling has mismatch probability at most $\delta$ [LPW, Proposition 4.7][LPW]. There are at most $N-t$ such comparisons. A union bound bounds a mismatch by $(N-t)\delta$. This coupling is an analytic comparison, not another actual sample, acquisition port or source operation.

If no such mismatch occurs and the actual $T_4\le N$, all future letters through completion agree. The unchanged original updates then give identical current records, future derived events, fourth marker and Stop. Completion on the Read reaching $N$ is included: pending prediction is already the prescribed deterministic Stop, even when the monitor has just overflowed. Beyond the boundary both coupled marginals may continue according to their own full laws; the remaining possible discrepancy is charged by the actual event $T_4>N$. The coupling inequality therefore gives

$$
e_{\rm law}^O(h)=e_{\rm conf}^O(h)
\le (N-t)_+\delta+\Pr_\mu(T_4>N\mid H_3=h).
\tag{2.5}
$$

When $t\ge N$, the same bound holds because $T_4>t\ge N$ on that third-latch atom and TV is at most one. The supplied injective transcript map includes all future letters, not just the fourth outcome, so this is a bound for the required complete residual law.

Multiply (2.5) by the actual $p_\mu(h)$ and sum over the whole stopping partition. The tower identity and (1.4) give

$$
\mathcal A_{\rm law}^\mu(O)=\mathcal A_{\rm conf}^\mu(O)
\le N2^{-b}+\Pr_\mu(T_4>N)
\le N2^{-b}+\frac{183}{14N}.
\tag{2.6}
$$

No synthetic history weights, independently mixed segments or favorable-history condition enter this calculation. In particular future overflow is paid even when the queried $h$ itself has not overflowed; exact full-tail decoding before overflow is not claimed.

Choose finite $N>2C/\varepsilon$ and $b\ge4$ with $N2^{-b}<\varepsilon/2$. Both averages are then below $\varepsilon$. Nonnegativity and $\mathcal F_{\rm det}\subset\mathcal F_{\rm coh}$ prove the four zero infima.

### 2.4 Nonattainment from the existing positive-history theorem

For this very fixed $\mu$, [PC, Theorem 2.1][PC], consuming [ST, §§3.1,3.3][ST], gives for every finite complete observer in the larger randomized class

$$
\sup_{h\in\mathcal H_3}e_{\rm law}^O(h)
\ge\rho_p=\frac{1116529}{22781250}>0.
\tag{2.7}
$$

If $\mathcal A_{\rm law}^\mu(O)=0$, nonnegative summands and the strictly positive weights (1.3) force $e_{\rm law}^O(h)=0$ at every finite $h\in\mathcal H_3$, contradicting (2.7). Thus its average is positive. TV convexity gives $\mathcal A_{\rm conf}^\mu(O)\ge\mathcal A_{\rm law}^\mu(O)>0$. The exclusion applies to the full randomized class and hence both subclasses here. No finite history need attain the worst-history supremum, and no common positive average lower bound over growing finite machines follows. This completes the proof.

## 3. Quantifiers, representation and resource boundaries

**Approximation scope.** For each fixed $\mu$, choose $b_N\ge4$ with $2^{-b_N}\le N^{-2}$. Equation (2.6) gives both averages at most $197/(14N)$, tending to zero. For each fixed finite $h$, (2.5) also tends to zero: the conditional $T_4$ is almost surely finite and $N2^{-b_N}\to0$. The numerical average bound is uniform in $\mu$ for this family of prior-tailored installed tables. The quantifiers are $\forall\mu\,\forall\varepsilon\,\exists O_{\mu,\varepsilon}$; they do not install one prior-blind observer or sequence for every prior. A fixed table, program and initialization across all priors define a different optimization problem.

Every finite member still obeys the positive worst-history floor (2.7), so the convergence is not uniform over $\mathcal H_3$. The attained worst-history minima of [PC, Theorem 2.1][PC] remain $\rho_p$ on $\mathcal H_3,\mathcal H_p,\mathcal H_{\rm all}$ and $\rho_\beta=239/6750$ on $\mathcal H_\beta$, for both risks. Its existing models supply those attainers; the present approximants are not claimed to be worst-history minimizers. Randomization changes neither unrestricted finite-size average infimum nor nonattainment here. The two risks can differ for randomized competitors, and their optima or randomized advantages at a fixed complete budget are not decided.

**Complete finite account.** The monitor alone has $N(N+1)/2+1$ values. Its product with $C_0$ is a holding-field count, not a complete-machine minimum. Charge all original control, seed, bare fields, selector, records, latch and Stop status; the $O(N^2b)$-bit installed row table; the finite program and parameter descriptions; counters, table addresses, lookup workspace, output-description cursor and any finite simulation copy. Their alphabets are bounded for each fixed installation, so including them yields a finite complete configuration set. Counts are acquired through the actual updates; there is no free clock, posterior, $K$, $\rho$ vector, archive, continuous coordinate or persistent random tape.

The exhibited observer returns a finite rational generator description of a normalized countable law, not a materialized probability table for all transcripts. Optional sampling is a separate use of that description on a charged simulation copy with fresh source-independent fair bits. A dyadic row uses bounded $b$-bit workspace; the fixed $1/3$ continuation uses the bounded-workspace rational rejection sampler in [PC, §2.4][PC]. Generated letters never modify the live original control or count as actual source observations. Streaming needs no retained emitted prefix or unbounded cumulative index. A sampled transcript has almost surely finite length, bit consumption and runtime, with no finite worst-case bound. A receiver saving it pays its archive cost and gains no feedback archive for the observer. Arbitrary-word exact probability evaluation is a separate precision and workspace task.

Actual paid Reads, including every refusal and return after overflow, original record writes, installation, model description, arithmetic work, output, fresh randomness, elapsed time, energy and physical storage remain separate costs. Finite holding memory and finite rule description do not imply bounded sampled output, time or total physical resources. No state, table-size or scalar resource optimum is supplied.

**Ordinary existence and conditional effective production.** Even an unrepresented or noncomputable $\mu$ defines the finitely many real rows (1.2); their dyadic approximants exist as ordinary mathematics. Once chosen, only finitely many rational constants are installed. This gives no algorithm extracting them from an arbitrary unrepresented prior and no physical procedure installing or sampling such a prior.

A sufficient effective input is certified computability of the finitely many required $Z_\mu(a,d)$ and $Z_\mu(a+1,d)$. Computable masses with an effective depth-tail bound provide this: truncate only the installation computation, bound its omitted likelihood sum by the certified prior tail mass, and approximate the finitely many remaining terms. Since

$$
Z_\mu(a,d)\ge3^{-(a+d)}>0,
\tag{3.1}
$$

certified finite-precision division computes each ratio to any requested error. Compute a ratio approximation with error less than $\delta/4$, round it to the nearest $2^{-b}$ grid point, and clip to $[1/4,1/2]$. The error is less than $3\delta/4$, because the true ratio belongs to that interval; no equality-at-a-tie decision is needed. This constructs the finite table effectively under the stated representation contract, during charged installation. It neither truncates the actual prior/source nor grants runtime access to its sums. Physical source preparation, freshness and fair-bit authenticity remain external premises.

**Unresolved objectives.** Fixed-budget average optima, classification of optimal controllers or all attainers, total resource optimization, the original deadline-four memory classification, and general acquisition or global relational reconstruction remain separate pending problems. Predicting a conditional law does not recover the erased past, identify the realized hidden $K$ exactly, or determine the future realized transcript or physical duration.

## 4. Suppliers and the source-specific addition

| Supplier | Exact use and limit |
| --- | --- |
| [PC][PC], pin `1b27ec30e865e4fba864033fffed5ab2ba02fa6f`, Definitions 1.2–1.5, Theorem 2.1, §§2.1,2.4,4 | Original all-prior contract, complete transcript bridge, global compatibility pair, finite-law descriptions and positive attained worst-history minima. Its §4 leaves actual-history averages distinct. Those minima and their proofs are reused. |
| [FR][FR], same pin, §§9,13,15,20–26 | Acquired-count likelihood rows, legal overflow memory and existing actual-weighted terminal averages for finite rational support. §13 excludes overflow raw-tail accuracy; §§21–26 give countable-prior exact law/window recovery with separate precision and representation obligations, not the finite coherent average theorem here. |
| [ST][ST], pin `c5408c868deab35a192a8ed9105f2838a80a155d`, §§2.1,3.1,3.3,4 | Full stopped laws, all-countable finite positive-history lower witnesses, distinct randomized risk orders and the terminal/full-law distinction. No reproof of its lower witness construction is needed. |
| [BD][BD], pin `c633bce93ac6ffd5fa44ae3d9489c87c7557a531`, §§94.3,96.1,97.1,100.1,105.1,114.1 | Restored same-source Reads, stopped freshness, paid seed retries, original parser, total Read expectation and original Stop/receiver restrictions. No independent resampling or extra receiver information is transferred. |
| [E1][E1], pin `c5408c868deab35a192a8ed9105f2838a80a155d`, §2 | Causal record update on the full marker tree, third-write-before-latch and holding. Its accepted-cell past-recovery restriction does not restrict $\mathcal H_3$. |
| Levin–Peres, with Wilmer, [*Markov Chains and Mixing Times*, second edition][LPW], §4.2, Proposition 4.7, pp.50–52 | Mature TV coupling principle, applied to the two-letter rows in the live proof. Its finite-chain mixing objectives are not a supplier of this stopped-source average theorem. |

The addition is `repo-derived`: finite approximate likelihood rows and their same-update full continuation, the complete-tail bound (2.5) averaged under the actual whole $H_3$ law, and the resulting all-prior zero/unattained values. Existing terminal average constructions, exact conditional-law recovery and worst-history results are credited above. Rational approximation, Bayes conditioning, TV convexity, coupling, the tower identity and Markov's inequality are mature tools, not new general results. No generic memory framework or publication-priority claim is made. The theorem is ordinary mathematics; finite arithmetic corroboration cannot replace its countable-prior and unbounded-tail proof, and it has no Lean kernel verification.

[PC]: https://github.com/the-omega-institute/trureturing/blob/1b27ec30e865e4fba864033fffed5ab2ba02fa6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[FR]: https://github.com/the-omega-institute/trureturing/blob/1b27ec30e865e4fba864033fffed5ab2ba02fa6f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md
[ST]: https://github.com/the-omega-institute/trureturing/blob/c5408c868deab35a192a8ed9105f2838a80a155d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[BD]: https://github.com/the-omega-institute/trureturing/blob/c633bce93ac6ffd5fa44ae3d9489c87c7557a531/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/c5408c868deab35a192a8ed9105f2838a80a155d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[LPW]: https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

## 追加锚（本行以下为增补区）

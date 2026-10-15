---
slug: rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift
bibkey: rajchelkorzekwapuchalazyczkowski2021birkhoff
doi: 10.1063/5.0046581
url: https://arxiv.org/abs/2101.11288
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result
---

# A circulant unistochastic matrix without a circulant unitary lift

## Problem

G. Rajchel-Mieldzioć, K. Korzekwa, Z. Puchała and K. Życzkowski, *Algebraic and geometric structures inside the Birkhoff polytope*, arXiv:2101.11288, J. Math. Phys. 63, 012202, DOI 10.1063/5.0046581, Section IV, states:

> Conjecture 19. The sets Cd ∩ Ud and Cd² coincide for all d, i.e., for every circulant unistochastic matrix it is possible to find a corresponding circulant unitary matrix.

The universal assertion is **Refuted** at dimension ten. [Preregistration #16445](https://github.com/the-omega-institute/trureturing/issues/16445) fixes the source, quantifiers and Lean conventions. Definition 6 defines doubly circulant unistochastic matrices as those having a circulant unitary realization. The source quotations and locator are in [the existing Library note](../Library/QuantumBounds/rajchelkorzekwapuchalazyczkowski2021birkhoff.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every dimension $d$ | `claim` quantifies over natural $d$ | No restriction to even or positive dimensions in the assertion |
| Every circulant matrix $B$ | Every real `Matrix (Fin d) (Fin d)` with the reused `IsCirculant` | `Matrix.circulant` uses $v(i-j)$ with modular indices; the source's reversed convention describes the same class |
| Unistochastic $B$ | Reused `IsUnistochastic`, using `Matrix.unitaryGroup` and `RHLinalg.normSqMatrix` | Allows every complex unitary realization, including a real orthogonal one |
| A corresponding circulant unitary matrix | `HasCirculantLift` quantifies over a complex vector $z$, requires its circulant to be unitary, and requires entrywise squared norms to equal $B$ | The full source condition, with no certificate restriction |
| Equality of the two sets | `claim` gives the inclusion from circulant unistochastic matrices to matrices with a circulant unitary lift | The reverse inclusion follows from the source definitions |
| Refutation of the all-dimensional claim | `result` proves the literal negation of `claim` | One instance at $d=10$ suffices |

All binders and conjuncts implement these clauses. There is no additional hypothesis on $B$ or on a realizing unitary. `HasCirculantLift` mirrors Definition 6 verbatim: “The set of d × d doubly circulant unistochastic matrices Cd² consists of these circulant unistochastic matrices for which there exists the corresponding unitary matrix that is circulant.” `claim` mirrors the quoted Conjecture 19. The two other source predicates are reused from `CirculantBraceletNonUnistochastic`, without aliases.

## Motivation

The source's Lemma 18 supplies circulant unitary lifts at dimensions at most four. A circulant pattern of squared moduli does not require a realizing unitary's phases to be circulant. The obstruction tests precisely this distinction.

The [companion bracelet-sufficiency dossier](rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency.md) settles a different question of the same paper at dimension twelve. Its result is not a premise of this refutation; this module uses its frozen definitions of circulantness and unistochasticity.

## Gap

The all-dimensional extension of Lemma 18 fails. A common circulant phase pattern is inconsistent on the support below, although a unitary with row-dependent signs realizes the squared moduli.

The literature screen recorded in #16445 and the independent search report covers the source, Rajchel-Mieldzioć's thesis arXiv:2204.13008, Sections 2.9, 2.10 and 6.2, five distinct citing works from six citation records, author records, arXiv:2305.17978, and the quantum-embeddability paper Quantum 8, 1404. No prior resolution of Conjecture 19 was found in that scope. The citing-paper texts screened were arXiv:2604.02309, 2505.08785, 2405.05785, 2312.00497 and 2310.03436. These are attributed search readings, not a proof of literature completeness or priority.

## Route

Use zero-based indices $i=5a+r$ and $j=5b+s$, where $a,b\in\{0,1\}$ and $r,s\in\{0,1,2,3,4\}$. Put

$$
Q_{ij}=(-1)^a\mathbf1_{s=r+1\pmod5}-(-1)^b\mathbf1_{r=s+1\pmod5},\qquad
W=3I+2Q,\qquad U=W/5.
$$

The private integer certificate `int_orthogonal` checks $WW^{\mathsf T}=25I$. The consumed `u_unitary` transfers it to the complex unitary group. The private `b_eq` identifies $B=\operatorname{normSqMatrix}(U)$ with a circulant whose first row is

$$
\frac1{25}(9,4,0,0,4,0,4,0,0,4).
$$

`b_circulant` and `b_unistochastic` supply the two hypotheses of `claim`. These are the internal mathematical steps used by `result`; there is no extra public witness theorem.

## Falsifier

A hypothetical circulant unitary lift has coefficients $z_s$ nonzero exactly on $S=\{0,1,9,4,6\}$. The private `lift_moduli` and `support_from_moduli` obtain that support. The private `sparse_rows` projects row orthogonality at shifts $1,4,3$ to

$$
z_0\overline{z_9}+z_1\overline{z_0}=0,\qquad
z_0\overline{z_6}+z_4\overline{z_0}=0,\qquad
z_4\overline{z_1}+z_9\overline{z_6}=0.
$$

Conjugating the first equation and combining it with the second gives $z_9\overline{z_6}=z_4\overline{z_1}$. The third then forces $2z_9\overline{z_6}=0$. Both factors are nonzero. The consumed `phase_product_zero` and `no_circulant_lift` implement this contradiction, and `result` refutes `claim`.

## Evidence

The settling declaration is `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result` in [the Lean module](../D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.lean). The public surface is `HasCirculantLift`, `claim`, and `result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. All ten private theorem helpers are bind-only steps with live consumers. The module's admission basis is `open-problem-resolution (#16445; Refuted)`; its utility is a certified instance with `basis=refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Exact integer and support checks](https://github.com/the-omega-institute/trureturing-experiments/tree/4ebd7f4bee5948aae8c7d0176677067f8d06412f/docs/reports/rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift), at commit `4ebd7f4bee5948aae8c7d0176677067f8d06412f`, contain `check.py`, SHA-256 `e520ad5be3ed1928b5e41c135e3f6d856b3aa904dd7d3ccfd63f70ed4a68c568`. The independently rerun command `python3 /Users/auric/trureturing-experiments/docs/reports/rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift/check.py` exits 0 and reports `ALL_OK`.

The tested scope is exactly $N=10,12,\ldots,30$, with $\alpha=3/5$, $\beta=2/5$. It checks integer-scaled orthogonality, every squared entry against the circulant first row, and the three exact support overlaps. It does not compute variable parameters, all even dimensions, or a numerical phase search.

## Triage

### What the settlement shows

1. **Kernel-checked — mechanism at $d=10$.** `result`, through `int_orthogonal`, `u_unitary`, `b_eq`, `sparse_rows`, `phase_product_zero` and `no_circulant_lift`, establishes the stated circulant unistochastic instance and the impossibility of its circulant lift. Shifts $1$ and $m-1=4$ tie the four off-diagonal phases to $z_0$; shift $m-2=3$ adds two equal nonzero terms. The realizing matrix is the explicitly defined real matrix $U$, viewed over $\mathbb C$. Its signs vary along the two fibres of $\mathbb Z_2\times\mathbb Z_5$, which a circulant coefficient vector cannot do.

2. **Proved in prose — family for every even $N\ge10$.** Let $N=2m$ with $m\ge5$, and let $\alpha,\beta>0$ satisfy $\alpha^2+4\beta^2=1$. Let $T$ be the $m$-cycle shift and $R=\begin{pmatrix}1&1\\-1&-1\end{pmatrix}$. Set $Q=R\otimes T-R^{\mathsf T}\otimes T^{\mathsf T}$ and $U=\alpha I+\beta Q$. Then $R^2=(R^{\mathsf T})^2=0$ and $RR^{\mathsf T}+R^{\mathsf T}R=4I$, while $TT^{\mathsf T}=T^{\mathsf T}T=I$. Therefore $Q^{\mathsf T}=-Q$ and $Q^2=-4I$, so $UU^{\mathsf T}=(\alpha^2+4\beta^2)I=I$. Its diagonal squared entries are $\alpha^2$ and its other nonzero squared entries are $\beta^2$ at offsets $\{1,N-1,m-1,m+1\}$; the two block signs disappear on squaring. Thus $B$ is circulant and orthostochastic.

   For $S=\{0,1,N-1,m-1,m+1\}$, the pairs $(s,s-h)$ in $S\times S$ are exactly $(0,N-1),(1,0)$ at $h=1$; $(0,m+1),(m-1,0)$ at $h=m-1$; and $(m-1,1),(N-1,m+1)$ at $h=m-2$. This enumeration follows by subtracting those five residues, using $m\ge5$ to keep the residues distinct. A lift would have precisely this support. Set $u=z_0/\overline{z_0}$, with $|u|=1$. The first two equations give $z_1=-u\overline{z_{N-1}}$ and $z_{m-1}=-u\overline{z_{m+1}}$. Consequently $z_{m-1}\overline{z_1}=z_{N-1}\overline{z_{m+1}}$. The third forces twice this nonzero product to vanish, a contradiction. This all-dimensional and variable-parameter derivation is a prose proof, not an additional Lean theorem.

   Positivity is the preregistered family condition and is necessary for this support argument. The equation $\alpha^2+4\beta^2=1$ alone includes degenerate cases: $\beta=0$ gives $B=I$ with a circulant unitary lift. The refutation family does not include those cases.

3. **Computed — finite family checks.** The experiment verifies the fixed rational parameters at every even $N$ from 10 through 30 and exactly the orthogonality, squared entries and overlap pairs stated in its Evidence entry. The command exits 0; its pinned script and SHA-256 are given there. The computation does not establish an unbounded family; item 2 supplies the separate prose proof.

4. **Open — other dimensions.** Odd $d\ge5$, and even $d=6,8$, are not decided by this instance, the prose family, or the finite computation. Lemma 18's source result for $d\le4$ retains its scope.

5. **Literature boundary — spectral characterization.** The source's Fourier/spectral characterization of doubly circulant matrices remains applicable on $C_d^2$. The refutation shows that this set is a proper subset of $C_d\cap U_d$ at $d=10$. It does not invalidate the characterization on its stated domain or give a characterization of all circulant unistochastic matrices; that broader characterization is open here. No claim of a new kernel-checked spectral theorem is made.

The companion settlement concerns bracelet sufficiency, and Conjecture 9 is not settled here. Any use of Conjecture 19 to identify all circulant unistochastic matrices with $C_d^2$ has a false premise in dimension ten. Results proved for $C_d^2$, and the source's dimension-at-most-four results, retain their stated conditions.

## ASSUMED-UNVERIFIED

The source and literature screens are attributed to the orchestrator and the independent search/probe seats as recorded in #16445 and their reports. No answer was found in the searched scope; literature completeness and priority remain `ASSUMED-UNVERIFIED`. The pinned experiment was independently rerun. Only the dimension-ten settlement is kernel-checked in this module; the even-dimensional, positive-parameter family is proved in prose, and the finite experiment has the exact scope stated above. No minimal counterexample dimension is claimed.

---
slug: chruscinski-denisov-tarnowski-zyczkowski-2025-dissipator-spectral-disk-refutation
bibkey: chruscinskidenisovtarnowskizyczkowski2025spectral
doi: 10.1088/1751-8121/ae58d2
url: https://arxiv.org/abs/2504.07903v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result
---

# The pure-state scale does not confine purely dissipative spectra to the unit disk

## Problem

D. Chruściński, S. Denisov, W. Tarnowski and K. Życzkowski, *Spectral delineation of Markov generators: classical vs quantum*, arXiv:2504.07903v1 (2025), Section “Beyond complete positivity”, Conjecture 3. The source is `bounding_6.tex`, lines 1044–1050, md5 `31cb6e7a93cfb4dac99f83105a784d57`. The wording below is verbatim; the source's bra–ket macros are expanded for display:

> If $\mathcal{L}$ is a generator of positive trace-preserving dynamics and
>
> $\nu_{\text{q},3} := \max_{\|\psi\|=1} | \langle \psi|\mathcal{L}(|\psi\rangle\langle\psi|)|\psi\rangle|$,
>
> then the spectrum of $\frac{1}{ \nu_{\text{q},3}} \mathcal{L}$ is confined in the unit disk $\mathbb{D}(-1,1)$.

The disk is closed, with centre $-1$ and radius $1$. The paper sets its purely dissipative scope at lines 227 and 702. Its GKLS formula is at lines 205–209; the canonical traceless, Hilbert–Schmidt orthonormal jumps appear at lines 794–799. The source and publication identifiers are collected in [the literature note](../Library/QuantumContext/chruscinskidenisovtarnowskizyczkowski2025spectral.md).

Issue [#20152](https://github.com/the-omega-institute/trureturing/issues/20152) fixes the restricted reading: for every $N,m\in\mathbb N$, every finite family of traceless complex $N\times N$ jumps $L_k$ and nonnegative real rates $\gamma_k$, put $\mathcal L=\sum_{k\in\mathrm{Fin}\,m}\gamma_k\mathcal D_{L_k}$, where $\mathcal D_L(\rho)=L\rho L^\dagger-\tfrac12(L^\dagger L\rho+\rho L^\dagger L)$. Define $\nu$ as the supremum of $|\langle\psi|\mathcal L(|\psi\rangle\langle\psi|)|\psi\rangle|$ over $\sum_i|\psi_i|^2=1$. If $\nu>0$, every nonzero eigenmatrix $X$ with $\mathcal L(X)=\lambda X$ would satisfy $|1+\lambda/\nu|\le1$. This is `claim`; `result` refutes it.

## Motivation

The source seeks quantum analogues of the spectral enclosure for classical Markov generators. The pure-state quantity $\nu_{\text{q},3}$ is intrinsic to the generator and does not require its full spectrum. Conjecture 3 would make this quantity a universal enclosure scale even for positive trace-preserving dynamics. The source also proposes its optimality and a consequence for P-divisible time-dependent evolution. A counterexample within canonical purely dissipative GKLS dynamics tests these assertions without introducing negative rates or an explicit Hamiltonian term.

## Gap

The bounded literature check recorded in #20152 reports:

- arXiv lists only v1;
- Semantic Scholar lists two citing works, whose TeX the orchestrator read: arXiv:2605.30301 cites the source for random Lindbladians, and arXiv:2507.10669 does not discuss the delineation;
- OpenAlex counts zero citations of the journal version;
- the orchestrator's GitHub code search in `google-deepmind/formal-conjectures` for the arXiv identifier returned zero matches, and its repository search found no earlier record of the conjecture; issue #17999 mentions the paper as a citing work of another problem;
- the search report records no further discussion of Conjecture 3.

`not-found-in-searched-scope`. These are attributed search findings, not an exhaustive novelty claim.

## Route

Use coordinates $0,1,2$, as in Lean. Take $N=3$, $m=1$, rate $1$, and $V=\operatorname{diag}(1-i/3,-1-i/3,2i/3)$.

1. **Admissibility and the pure-state values.** The private lemma `witness_trace` gives $\operatorname{tr}V=0$. For $p_j=|\psi_j|^2$, `witness_expectation` expands the quadratic form to $(p_0-p_1)^2+p_2^2-(p_0+p_1+p_2)^2$. For a unit vector it is $-q$, where $q=1-(p_0-p_1)^2-p_2^2=4p_0p_1+2p_2(p_0+p_1)$, so $0\le q\le1$.
2. **The supremum has genuine witnesses and bounds.** The vector $(1,0,0)$ gives value zero, making the set nonempty. Every value is at most one, providing boundedness above. The unit vector $((1+i)/2,(1+i)/2,0)$ gives norm one. The private lemmas `witness_scale_upper` and `witness_scale_pos` supply precisely the bounds $0<\nu\le1$ used by the refutation; the latter proof also establishes $1\le\nu$ internally.
3. **An eigenmatrix.** For the nonzero matrix unit $X=E_{01}$, `witness_eigenvalue` gives $\mathcal D_V(X)=(-2+2i/3)X$.
4. **Separation from the disk.** For every real $0<\nu\le1$, the private lemma `outside_disk` gives $|1+(-2+2i/3)/\nu|>1$. Its squared norm minus one is $(40/9-4\nu)/\nu^2>0$. Applying `claim` to this eigenpair contradicts that strict inequality.

## Falsifier

The counterexample must belong to the source's class and use its scale. The relevant correspondences are:

- `dissipator` and `generator` are exactly the finite purely dissipative GKLS expression, with no Hamiltonian commutator. The only rate in the witness is strictly positive, so allowing zero rates in `claim` does not account for the refutation.
- `scale` is a real `sSup` of complex norms of the pure-state quadratic forms. For this witness its defining set is explicitly nonempty and bounded above, and the value one is attained. Thus its supremum agrees with the source's maximum in this example; no general maximum-existence theorem is needed here.
- The source's canonical normalization does not exclude the witness: $\operatorname{tr}(V^\dagger V)=8/3$, and replacing the jump by $\sqrt{3/8}\,V$ and its rate by $8/3$ leaves $\mathcal D_V$ unchanged and gives a traceless Hilbert–Schmidt normalized jump. This rescaling is an algebraic correspondence, not a separate assertion of `result`.
- `result` is a statement about matrices and their eigenpairs. It does not formalize semigroup positivity or trace preservation. The explicit Kraus-series argument below supplies the ordinary mathematical bridge from this witness to the source's positive trace-preserving dynamics.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.lean` (198 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.lean.json`, statement `sha256:7b0930187492dfe7a38b37bff544ff648de45df162036bbea25b95d090e32d04`.

Declaration statements:

- `result`: `sha256:9a90a94b3ca997c675bad3b7ede86e0996d3abd727978b0caaff4c4fec202752`;
- `claim`: `sha256:088555243bb98e7f2cfce3c69f62fc8c774ecbda7c403e4e5626117dcdfcd895`.

## Triage

Tier 1 conjecture of a 2025 preprint, preregistered in issue #20152 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion `claim` is false: nonnegative real rates, traceless complex jumps and strictly positive `scale` do not suffice to ensure $|1+\lambda/\nu|\le1$ for every nonzero eigenmatrix of the resulting finite sum of dissipators. The type is $\neg\mathrm{claim}$; it contains no assertion about arbitrary dimensions separately, semigroups, optimal scales or perturbations.

**Computed, not formalized** (independent exact rational arithmetic):

- Expanding the dissipator on all nine matrix units gives eigenvalue $0$ with multiplicity three, $-2\pm2i/3$ each with multiplicity one, and $-1\pm2i/3$ each with multiplicity two. The unit vector used in the Lean proof gives quadratic-form value $-1$, and $|1+(-2+2i/3)|^2=13/9$.
- Applying the source's finite spectral formula $R=\max_{\lambda\ne0}|\lambda|^2/(-2\operatorname{Re}\lambda)$ (TeX lines 765–781) to these eigenvalues gives $R=10/9$. For this representation, $\nu_{\text{q},2}=\max_j|v_j|^2=10/9$; canonical normalization gives $\nu_{\text{q},1}=8/3$. At those two scales, all nine computed eigenvalues lie in the respective disks: their shifted squared norms are among $\{1,37/100\}$ and $\{1,1/8,29/64\}$, respectively.
- On the rational probability grid $p=(a/d,b/d,1-(a+b)/d)$ with $1\le d\le40$, $a,b\ge0$, $a+b\le d$, all $12\,340$ tested triples, including repetitions, give the stated variance identity. For this tested grid, no violation of $0\le q\le1$ was observed. This finite check adds no assertion about untested vectors.

**Argued, not formalized**.

- *Mechanism and missing structure.* For one diagonal jump with entries $v_j$, the pure-state value is $|\sum_jp_jv_j|^2-\sum_jp_j|v_j|^2$, a negative variance. Adding the same scalar to all $v_j$ leaves that variance unchanged, by expanding the two terms and cancelling the scalar contributions. But the eigenvalue on $E_{ij}$ is $v_i\overline v_j-(|v_i|^2+|v_j|^2)/2$, with real part $-|v_i-v_j|^2/2$ and imaginary part $\operatorname{Im}(v_i\overline v_j)$. Here the variance attains one, while the eigenvalue has real part $-2$ and nonzero imaginary part $2/3$. At scale one the real part already reaches the disk's left endpoint; any nonzero imaginary part puts it outside. Tracelessness does not remove this phase contribution. Normality or unitality would not repair the assertion: $V$ is diagonal and $\mathcal D_V(I)=VV^\dagger-V^\dagger V=0$.
- *The dynamics really are completely positive and trace-preserving.* Put $B=V^\dagger V$. Since $V$ is diagonal, the maps $\rho\mapsto V\rho V^\dagger$, $\rho\mapsto B\rho$ and $\rho\mapsto\rho B$ commute. Expanding their exponentials gives $e^{t\mathcal D_V}(\rho)=\sum_{n\ge0}K_n(t)\rho K_n(t)^\dagger$, where $K_n(t)=e^{-tB/2}t^{n/2}V^n/\sqrt{n!}$ for $t\ge0$. The matrix series converges, and $\sum_nK_n(t)^\dagger K_n(t)=e^{-tB}\sum_n t^nB^n/n!=I$. Thus these maps are completely positive and trace-preserving, and the exponential supplies their semigroup law. This verifies the source-class correspondence without treating it as a Lean conclusion.
- *A surviving restricted case.* For one nonzero traceless Hermitian jump, diagonalize it with smallest and largest eigenvalues $a<b$. For a probability distribution on its eigenvalues, $\mathbb E[(x-a)(b-x)]\ge0$ implies $\operatorname{Var}(x)\le(\mathbb Ex-a)(b-\mathbb Ex)\le(b-a)^2/4$. Equal weight on endpoint eigenvectors attains this bound. Hence $\nu=(b-a)^2/4$, while the dissipator eigenvalues $-(a_i-a_j)^2/2$ belong to $[-2\nu,0]$. The disk bound is therefore valid and sharp in this restricted case, matching the source's example at lines 1092–1104. This argument does not extend the conclusion to arbitrary sums of Hermitian jumps.
- *A sufficient replacement scale.* For $s>0$ and $\operatorname{Re}\lambda<0$, expanding $|1+\lambda/s|^2\le1$ gives exactly $s\ge|\lambda|^2/(-2\operatorname{Re}\lambda)$. Thus the source's full-spectrum scale $R$ remains sufficient whenever all nonzero eigenvalues have negative real part. For the present example, the variance calculation gives $\nu_{\text{q},3}=1$, below the computed $R=10/9$. The ordering $\nu_{\text{q},3}\le\nu_{\text{q},2}\le\nu_{\text{q},1}$ survives in this example; ordering alone does not make its smallest entry sufficient. The module does not settle the general disk conjectures for $\nu_{\text{q},1}$ or $\nu_{\text{q},2}$.
- *Effect on dependent statements of the source.* Conjecture 3 and the universal optimality assertion immediately following it (line 1051) cannot stand under the stated purely dissipative scope: the proposed scale is not even sufficient. The corollary at lines 1202–1209, asserting the same enclosure for P-divisible dynamics, is also contradicted by taking the constant generator $\mathcal L_t=\mathcal D_V$. Its propagators $e^{(t-s)\mathcal D_V}$ are completely positive and trace-preserving by the preceding argument, hence positive, while the disk bound is violated. Leaving this disk alone therefore cannot certify a loss of P-divisibility. The universal $\nu_{\text{q},3}$ enclosure and optimality language in the Conclusions and the universal interpretation of that scale in the summary figure require restriction. The source's numerical ensembles remain evidence about those tested ensembles; they do not supply the missing universal enclosure. The independent classical results and the single-Hermitian-jump calculation are not refuted by this example.

## ASSUMED-UNVERIFIED

The bounded literature check in #20152 does not establish exhaustive worldwide novelty or priority. The citation counts, the two citing-paper readings, the code search and the earlier repository search are attributed to the orchestrator and were not independently reproduced. The issue's assertion that the conjecture persists in the 2026 journal version is search-reported; that version was not read. The quotation and source-dependent analysis here use the directly checked arXiv v1 TeX.

The full nine-eigenvalue calculation, the larger scaling parameters and the finite probability-grid check are computations, not additional Lean declarations. The general variance interpretation, canonical normalization, Kraus-series bridge, Hermitian restricted case, replacement-scale criterion and consequences for the source's dependent statements are mathematical arguments, not assertions formalized by this module. The paper's random sampling was not reproduced. The perturbative-family computations and all-dimension open-set persistence reported in #20152 were not reproduced or verified; no such extension is established here. A general classification of additional hypotheses restoring the pure-state enclosure remains outside this settlement.

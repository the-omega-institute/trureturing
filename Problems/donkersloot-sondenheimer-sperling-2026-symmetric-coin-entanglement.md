---
slug: donkersloot-sondenheimer-sperling-2026-symmetric-coin-entanglement
bibkey: donkerslootsondenheimersperling2026walks
doi: 10.48550/arXiv.2603.24679
url: https://arxiv.org/abs/2603.24679v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.result
---

# The symmetric coin maximizes full-mode entanglement of the Hadamard walk on every finite circle

## Problem

E. K. F. Donkersloot, R. Sondenheimer and J. Sperling, *Multipartite entanglement dynamics in quantum walks* (2026), arXiv:2603.24679v1, Section III C 2, “Arbitrary localized initial conditions”, state in `arxiv-v1.tex`, lines 653–654:

> Hence, we expect this walk to always yield the maximum entanglement.
> This is indeed the observed behavior for all graph sizes and time steps we have tested.

The preceding sentence, line 652, identifies the initial coin by $\theta=\phi=\pi/2$. The walk, measure and initial states are specified in Sections II A–C and the localized initial-state equation at TeX lines 423–425, respectively; see [the literature note](../Library/Entropy/donkerslootsondenheimersperling2026walks.md).

For $P\ge1$, the modes are $(b,x)\in\{0,1\}\times\mathbb Z/P\mathbb Z$. The evolution is $T=S(H\otimes I)$, where $H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and $S$ shifts coin component $0$ left and component $1$ right, periodically. A normalized coin $c=(\alpha,\beta)$ starts at position zero. Write $\lambda_{P,n,c}=T^n(c\otimes|0\rangle)$ and $c_*=(1,i)/\sqrt2$.

For a finite amplitude family $\lambda$, the encoded single-photon vector is $|\psi_\lambda\rangle=\sum_k\lambda_k|1_k\rangle$, with one tensor factor per mode. The module defines $g_{\max}(\lambda)=\sup_{\|z_k\|=1}|\langle\bigotimes_k z_k|\psi_\lambda\rangle|^2$, with $z_k\in\mathbb C^2$, and $E_g(\lambda)=1-g_{\max}(\lambda)$.

Issue [#22527](https://github.com/the-omega-institute/trureturing/issues/22527) fixes the reading: for every natural $P\ge1$, every $n\in\mathbb N$ and every $c\in\mathbb C^2$ with $|\alpha|^2+|\beta|^2=1$, $E_g(\lambda_{P,n,c})\le E_g(\lambda_{P,n,c_*})$. This is proved, including $P=1$ and $n=0$.

## Motivation

For each circle size and time, the question asks which localized initial coin produces the most geometric entanglement across the individual optical modes. The result supplies one optimal coin uniformly in both parameters. It addresses the single-photon, full-partition measure used in Section III C 2; the source also studies other partitions and several walkers, which require different comparisons.

## Gap

The bounded literature check recorded in #22527 reports:

- the arXiv v1 source retains the expectation with numerical support;
- the orchestrator's Zenodo check finds the authors' code release, and the arXiv record lists only v1;
- searches of Zenodo, ResearchGate, SSRN and GitHub for the title and quoted expectation find no settlement;
- the repository search finds no earlier record of the paper, and the published open-problems page has no entry for it.

The search conclusion is `not-found-in-searched-scope`. The checked v1 TeX contains the quoted expectation; the other search readings are attributed to the preregistration and remain bounded as specified below.

## Route

All lemma names below refer to the canonical module, including its private helpers.

1. **The supremum and phases.** For any finite mode type and any complex amplitude family, `overlap_bounded` bounds the squared overlaps above, and `overlap_attained` supplies unit local factors attaining `gMax`. The admissible factors form a nonempty compact set: the constant family $(1,0)$ is admissible, and the overlap is continuous. Thus the real supremum is used with nonemptiness and boundedness established. For two amplitude families on the same finite mode type with equal squared moduli at every mode, `phase_invariance` gives equal `gMax` values. For a nonnegative real amplitude family, `positive_max` supplies maximizing real local factors with nonnegative coordinates and squared local norms equal to one.

2. **Balancing two distinct modes.** For nonnegative real $a,b,r,s$, `two_factor_max` computes the maximum of $(a x_0y_0+b s x_0y_1+b r x_1y_0)^2$ over real vectors satisfying $x_0^2+x_1^2=y_0^2+y_1^2=1$ as $(C+\sqrt{C^2-4b^4r^2s^2})/2$, where $C=a^2+b^2(r^2+s^2)$, and supplies nonnegative maximizing vectors. At fixed spectators, $a$ is their single-excitation contribution and $b$ their vacuum product; both are nonnegative for the factors supplied by `positive_max`. Increasing $r^2s^2$ while preserving $r^2+s^2$ cannot increase this expression. Precisely, `pair_balancing` applies to arbitrary complex families $\lambda,\mu$ on a finite mode type and distinct modes $i,j$, provided $|\mu_k|^2=|\lambda_k|^2$ for every $k\ne i,j$, $|\mu_i|^2+|\mu_j|^2=|\lambda_i|^2+|\lambda_j|^2$, and $|\lambda_i|^2|\lambda_j|^2\le|\mu_i|^2|\mu_j|^2$. Its conclusion is $g_{\max}(\mu)\le g_{\max}(\lambda)$. No normalization or nonzero-amplitude assumption is required by this lemma.

3. **Reflection pairs in the walk.** For all natural $P,n$, `walk_linearity` expresses the evolution of every complex coin through the two basis-coin evolutions $u=T^n|0,0\rangle$ and $w=T^n|1,0\rangle$. For all such $P,n$, `walk_reflection` makes these two amplitude families real and gives $u(1,-x)=-(-1)^n w(0,x)$ and $w(1,-x)=(-1)^n u(0,x)$ for every $x\in\operatorname{ZMod}P$. For all natural $P,n$ and every unit coin $c$, `walk_pair_probabilities` gives, at every $x$, equal probabilities for $c_*$ at $(0,x)$ and $(1,-x)$, whose sum equals the corresponding pair sum for $c$. In particular, if $u(0,x)=a$ and $w(0,x)=b$ with $a,b\in\mathbb R$, each $c_*$ probability is $(a^2+b^2)/2$; the cancellation uses the unit-coin hypothesis.

4. **All pairs.** For positive $P$, `pair_average_le` applies to any complex amplitude families on $\operatorname{Fin}2\times\operatorname{ZMod}P$ whose second family has equal squared moduli within every pair $(0,x),(1,-x)$ and the same pair sums as the first. It gives $g_{\max}(\mu)\le g_{\max}(\lambda)$ by applying `pair_balancing` over the finite set of positions. The two members of each pair are distinct because their coin labels differ, including when $P=1$. Applying this to the two walk states using `walk_pair_probabilities`, under $P\ge1$ and a unit initial coin, and subtracting the overlap comparison from one gives `result : claim`.

## Falsifier

The settlement would miss the source question if the evolution, partition or overlap differed from the source's. The module defines the Hadamard flip followed by the periodic controlled shift, localizes the coin at zero, represents a single excitation on the $2P$ modes, and takes the squared complex inner product with products of unit two-component local factors. `UnitSpinor` means exactly that the sum of the two squared complex moduli is one. Its comparison has no finite-time cutoff.

The distinction between the source's optical Fock factors and the module's vacuum/one-photon factors, and preservation of normalization by the recurrence, have the explicit arguments below; they are not additional conclusions of `result`. The theorem asserts maximality without uniqueness, an infinite-line limit, a change of walk coin, or optimization for another partition.

## Evidence

The canonical source is `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.lean.json`.

Declaration statements:

- `result`: `sha256:cceb3a76b14b26e5d1efae3710204e0d4c8c541d1ac960dc981601a3d13743be`;
- `claim`: `sha256:54f978c2042c0f627552979cbe56a83cbc2d175ef80acbd58dbdff60da1042ef`.

## Triage

Tier 1 expectation with numerical support in a 2026 preprint, preregistered in issue #22527 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $P\ge1$, every natural time $n$ and every normalized complex two-component coin $c$ localized at position zero, the geometric entanglement defined above for `walkState P n c` is at most that for `walkState P n cStar`.

**Computed, not formalized** (the orchestrator, Claude Code/Opus, recorded in #22527): for $P\in\{2,3\}$, $n\in\{1,2,3\}$ and six random initial coins in each case, a numerically estimated $E_g$ exceeding that of $c_*$ was not observed for the tested family.

**Argued, not formalized.**

- *Normalization and the optical interpretation.* For complex $a,b$, $|(a+b)/\sqrt2|^2+|(a-b)/\sqrt2|^2=|a|^2+|b|^2$. For $P\ge1$, both periodic shifts permute the finite positions, so summing this identity gives preservation of the squared norm by each step; iteration preserves a unit initial coin's norm. Also, for a single-photon vector, only the vacuum and one-photon coordinates of each local Fock factor contribute to any product overlap. Projecting each unit factor onto these coordinates gives norm at most one. If every projection is nonzero, normalizing the projections cannot decrease the squared overlap; a zero projection gives zero overlap. Conversely, two-component factors embed as Fock factors. The two suprema therefore agree.
- *Attainment and nonuniqueness.* The inequality is attained by the normalized coin $c_*$. For every $P\ge1$ and $n\in\mathbb N$, `walk_reflection` gives real basis-coin evolutions, and `walk_linearity` consequently makes the evolution from $\overline{c_*}=(1,-i)/\sqrt2$ the conjugate of the evolution from $c_*$. These amplitude families have equal squared moduli at every mode of the same finite mode type, so `phase_invariance` gives equal `gMax`, hence equal $E_g$. Both coins have unit norm and are not related by a global phase. Thus uniqueness up to global phase cannot be added to the statement; a classification of all maximizing coins is open here.
- *The interpolation observation.* In Section III C 2, line 665, the source states: “There, we observe a monotonous increase in $E_g$ at every time step for increasing $\theta = 0 \to \pi/2$.” For fixed $P\ge1$ and $n\in\mathbb N$, put $c_\theta=(\cos(\theta/2),i\sin(\theta/2))$. The real amplitudes and reflection identities of `walk_reflection`, together with `walk_linearity`, give reflection-pair probabilities $a^2\cos^2(\theta/2)+b^2\sin^2(\theta/2)$ and $b^2\cos^2(\theta/2)+a^2\sin^2(\theta/2)$. Their sum is fixed and their difference is $(a^2-b^2)\cos\theta$. For $0\le\theta_1\le\theta_2\le\pi/2$, the pair product therefore cannot decrease. Replacing the finitely many distinct reflection pairs one at a time preserves squared moduli off the chosen pair and preserves its sum, so every hypothesis of `pair_balancing` holds at each replacement. This gives a nondecreasing $E_g$ along this interpolation. This ordering between intermediate coins is an argument beyond the compiled type of `result`.
- *Effect on the source's other claims.* The full-partition, finite-circle maximality expectation in lines 653–654 has the proved reading above, and supplies the endpoint bound for the interpolation illustrated in the source's figure. The source's stronger monotonic interpolation observation has the separate argument just given. Its conjecture in lines 645–649 about the asymptotic local-maximum great circle on the infinite line remains open here: `result` supplies neither an infinite-line limit nor a characterization of a contour of local maxima. The source's other partitions and multi-walker scenarios are outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #22527 does not establish exhaustive worldwide novelty or priority. Its Zenodo, repository and open-problems-page searches, and the searches attributed there to GPT Pro on Zenodo, ResearchGate, SSRN and GitHub, were not reproduced for this dossier. The fetched arXiv record lists only v1 and gives the arXiv-issued DOI used above, which the Library note also records. No journal DOI or journal reference is listed in the checked record.

The numerical reading attributed to the orchestrator was not reproduced, and a product-state numerical optimization is not a certificate of its global optimum. The statements in “Computed, not formalized” and “Argued, not formalized” are not additional compiled conclusions of the module. In particular, norm preservation, the full-Fock-space comparison, maximality of the conjugate coin and monotonicity along the interpolation have the arguments above but no separate formal declarations here. The classification of maximizing coins, the source's asymptotic great-circle conjecture, and extensions to other coins, partitions, topologies or multiple walkers remain open in this dossier.

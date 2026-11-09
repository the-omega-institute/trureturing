---
slug: ducuara-susa-skrzypczyk-2024-f3-steering-ellipsoid-threshold
bibkey: ducuarasusaskrzypczyk2024hidden
doi: 10.1103/PhysRevA.110.022435
url: https://arxiv.org/abs/2406.03945v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.result
---

# The $\mathrm F_3$ steering inequality has the sharp ellipsoid-centre threshold two thirds

## Problem

A. F. Ducuara, C. E. Susa and P. Skrzypczyk, *Locally inaccessible hidden quantum correlations*, Phys. Rev. A **110**, 022435 (2024), arXiv:2406.03945v1, state the QSE conjecture in `QC_LI.tex`, lines 282–284:

> For any two-qubit state $\rho \in D(\mathds{C}^2 \otimes \mathds{C}^2)$, its maximal violation of the $\rm CHSH$-inequality \eqref{eq:HC} and the $\rm F_3$-inequality \eqref{eq:CAC} are upper bounded by functions that depend on the magnitude of the QSE's centre as ${\rm B}(\rho) \leq f_{\rm CHSH}(c_B)$ and ${\rm F_3}(\rho)\leq f_{\rm F_3}(c_B)$, respectively. With $c_B=|\bm{c}_B|$.

Line 288 asks:

> Exploring the form of function $f_{\rm F_3}(c_B)$ is an interesting task which we leave for future research.

The same line describes the numerical thresholds:

> In particular, we highlight that there seem to exist values $c_{\rm \, CHSH}=0.5$ and $c_{\rm \, F_3} = 0.66$, such that states with QSE centres' magnitudes greater than these values, can no longer lead to a violation of the $\rm CHSH$-inequality and the $\rm F_3$-inequality, respectively.

For a positive semidefinite trace-one complex two-qubit matrix $\rho$, write $\boldsymbol a$, $\boldsymbol b$ for its Bloch vectors and $T_{ij}=\operatorname{Re}\operatorname{tr}[\rho(\sigma_i\otimes\sigma_j)]$. The module defines Bob's centre by

$\boldsymbol c_B=(\boldsymbol b-T^{\mathsf T}\boldsymbol a)/(1-|\boldsymbol a|^2)$ when $|\boldsymbol a|\ne1$, and $\boldsymbol c_B=\boldsymbol b$ when $|\boldsymbol a|=1$; put $c_B=|\boldsymbol c_B|$.

Its $\mathrm F_3(\rho)$ is the real supremum of

$\displaystyle \frac1{\sqrt3}\left|\sum_{i=1}^3\operatorname{tr}[\rho\,((\boldsymbol\alpha^i\cdot\boldsymbol\sigma)\otimes(\boldsymbol\beta^i\cdot\boldsymbol\sigma))]\right|$

over real unit Alice directions $\boldsymbol\alpha^i$ and real orthonormal Bob frames $\boldsymbol\beta^i$. The absolute value here is the complex norm. The source's Eq. (CAC), lines 209–214, gives its optimized value as $\sqrt{s_1^2+s_2^2+s_3^2}$, where the $s_i$ are the singular values of $T$; the relationship to the frame formulation is discussed below. The source definitions and locator are in [the literature note](../Library/Entropy/ducuarasusaskrzypczyk2024hidden.md).

Issue [#26164](https://github.com/the-omega-institute/trureturing/issues/26164) fixes the settlement as the conjunction of

$\displaystyle \mathrm F_3(\rho)\le\max\{\sqrt{3(1-c_B)},1\}$

for every positive semidefinite trace-one two-qubit matrix, and the existence, for every real $0\le t<2/3$, of such a matrix with $c_B=t$ and $\mathrm F_3(\rho)>1$. This conjunction is proved.

## Motivation

The source uses a centre-only impossibility region to detect hidden correlations that cannot be accessed by filtering on just one side. Its Result 2 (`QC_LI.tex`, lines 519–525) makes the one-sided $\mathrm F_3$ criterion conditional on the QSE conjecture and uses the estimated cutoff $0.66$. An analytical bound and an exact threshold supply the geometric ingredient needed by that criterion, with a correction to its numerical cutoff. They also separate this ingredient from the harder optimization over local filters.

## Gap

Issue #26164 records the bounded literature check before any Lean:

- the source TeX states the conjecture and requests analytical proofs in its concluding section, line 680; the issue also records the journal abstract as describing the conjecture as lacking an analytical proof;
- INSPIRE and OpenAlex list two citing works: S. Mukherjee and S. Paul, *Revealing Hidden Non n-Locality In n-Local Star Network*, arXiv:2506.19026v1, is reported to contain no $\mathrm F_3$ centre bound; the abstract of L.-L. Xing and H. Yang, *Bounding entanglement and Bell nonlocality for arbitrary two-qubit state via quantum steering ellipsoid*, Phys. Scr. **101**, 135103 (2026), DOI 10.1088/1402-4896/ae5354, concerns volume-based entanglement and CHSH bounds, while its full text was not read;
- the recorded search of 40 recent arXiv abstracts containing “steering ellipsoid”, through arXiv:2608.30037, found no centre bound for $\mathrm F_3$ or a steering inequality;
- the repository's [CHSH dossier](milne-jennings-jevtic-rudolph-2014-chsh-centre-bound.md) lists this $\mathrm F_3$ question as open, and the preregistration reports no existing dossier or issue settling it.

`not-found-in-searched-scope`.

## Route

The lemma names below belong to `SteeringEllipsoidFThreeThreshold` unless an owner is specified. Write $E=\sum_{i,j}T_{ij}^2$.

1. **Settings and the supremum.** For a Hermitian two-qubit matrix, three unit Alice directions and an orthonormal Bob frame, `setting_bound` bounds the setting value by $\sqrt E$. Its `frame_energy` input requires a real $3\times3$ matrix and an orthonormal frame and identifies $\sum_i|T\boldsymbol\beta^i|^2$ with $E$. The value set is nonempty for every two-qubit matrix by `values_nonempty` and bounded above for every Hermitian matrix by `values_bddAbove`. Thus `fThree_le_frobenius`, under the Hermitian hypothesis, bounds its genuine real supremum by $\sqrt E$.
2. **The summed flip bound.** For a positive semidefinite trace-one two-qubit matrix, `summed_flip` gives $2E+|\boldsymbol b|^2\le3+6\Delta$, where $\Delta=\operatorname{Re}\operatorname{tr}(\rho^2)-\operatorname{Re}\operatorname{tr}[(\operatorname{tr}_B\rho)^2]$. It applies `SteeringEllipsoidCHSH.flip_purity_identity`, whose hypotheses are Hermiticity, trace one and a real unit direction, to each coordinate direction. The flipped matrices are positive semidefinite, so their trace products with $\rho$ are nonnegative.
3. **An affine marginal bound.** For a positive semidefinite trace-one two-qubit matrix, put $c=|\operatorname{centre}(\rho)|$, the Alice-centre convention, and $r=|\boldsymbol b|^2$. The reused `SteeringEllipsoidCHSH.delta_le_centre`, with these same state hypotheses, gives $\Delta\le(1-r)(1/2-c)$. Hence `affine_bound`, also under positivity and trace one, gives $E\le3-3c+(3c-2)r$. Nonnegativity of a squared length and `SteeringEllipsoidCHSH.bob_radius_le`, requiring positivity and trace one, give $0\le r\le1$. The lemma `envelope` therefore gives $E\le\max\{3(1-c),1\}$ for every positive semidefinite trace-one matrix.
4. **Bob's centre.** For every two-qubit matrix, `swap_readouts` exchanges the Bloch vectors and centres and transposes $T$ under the party swap. For a positive semidefinite trace-one matrix, the swap preserves these state hypotheses and $E$. Applying `envelope` to the swapped matrix and `fThree_le_frobenius` to the original yields `universal_bound`, with precisely the positivity and trace-one hypotheses.
5. **A violating family below the threshold.** For real $t$ with $0\le t<2/3$, `threshold_parameters` gives $D=2-2t-t^2>0$ and $s=t(1-t)/D\in[0,1)$. The reused `SteeringEllipsoidCHSH.tight_psd` requires $0\le t$ and $s\le1$; `tight_readouts` requires $t\le1$ and $0\le s\le1$; `tight_centre` requires $0\le t\le1$ and $0\le s<1$. These hypotheses hold for the chosen parameters. They give a positive semidefinite trace-one state with Alice-centre length $t$ and correlation matrix $\operatorname{diag}(p,-p,q)$, where $p=\sqrt{1+s}\sqrt{(1-t)(1-s)}$ and $q=1-t+ts$. Under $0\le t<2/3$ and $s=t(1-t)/D$, `threshold_energy` gives $2p^2+q^2>1$. The lemma `balanced_setting` requires a Hermitian matrix, a correlation matrix of exactly this diagonal form and $2p^2+q^2>1$; it constructs an orthonormal Bob frame with equal image lengths and aligned unit Alice directions to obtain $\mathrm F_3>1$. Swapping `tightState t s` supplies the Bob-centre witness in `threshold_family`, whose hypotheses are exactly $0\le t<2/3$.

## Falsifier

The proof would not answer the registered question if the centre convention, admissible settings or supremum differed from the quantities under discussion. The module uses complex $4\times4$ matrices indexed by the two qubits, with positivity and trace one explicitly required by `claim`. Its Bloch readouts, Pauli matrices and Euclidean length are the reused `blochA`, `blochB`, `corr`, `pauli` and `vlen`; `spin` is the Pauli observable of a real direction.

The source centre formula, Eq. (QSEcentre), lines 246–261, is undefined at $|\boldsymbol a|=1$. The module explicitly assigns $\boldsymbol b$ there. Its frame optimization follows the preregistered reading of Eq. (CAC), rather than restricting Bob to one fixed coordinate frame. Neither existence of a maximizing setting nor boundedness of an arbitrary real supremum is assumed: the relevant nonemptiness and boundedness lemmas are given in the route. The claim concerns the sharp threshold for crossing one, without claiming an optimal envelope at each fixed centre length.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.lean`.

- **Proof.** It defines `centreB`, `fThreeValues`, `fThree` and `claim`, and proves `result : claim`.
- **Reuse.** It uses the Bloch readouts and Alice-centre convention of `SteeringEllipsoidFullyEntangledFraction`, the flip, purity, marginal and family lemmas of `SteeringEllipsoidCHSH`, and the existing Pauli spin and party-swap definitions.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.lean.json`.

Declaration statements:

- `result`: `sha256:0e4ea75016cc7a4f5417ffa01e8bc2d2f34b1aff02813335268ff554d7670088`;
- `claim`: `sha256:38be221805f2770a20d9ae9f95626f96d488eb42b2e1eb99ed746e7afa5d53e2`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #26164 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:**

- For every positive semidefinite trace-one two-qubit matrix $\rho$, $\mathrm F_3(\rho)\le\max\{\sqrt{3(1-|\operatorname{centreB}(\rho)|)},1\}$.
- For every real $t$ with $0\le t<2/3$, there is a positive semidefinite trace-one two-qubit matrix $\rho$ with $|\operatorname{centreB}(\rho)|=t$ and $\mathrm F_3(\rho)>1$.

**Computed, not formalized:** None.

**Argued, not formalized**

- *Decisive mechanism and scope.* For positive semidefinite trace-one matrices, `summed_flip` turns three nonnegative flip overlaps into a bound on the whole correlation energy; `affine_bound` reduces the remaining marginal dependence to an affine function of a number in $[0,1]$. The two endpoints give the two branches in `envelope`, under the same state hypotheses. No full-rank assumption occurs, and the centre definition covers a pure Alice marginal.
- *The source optimum.* For a Hermitian matrix and real directions, `setting_trace` identifies each expectation with $\boldsymbol\alpha\cdot T\boldsymbol\beta$. To see why optimizing Bob's frame gives the source's singular-value expression, let $Q=T^{\mathsf T}T$. There is an orthonormal basis with $\boldsymbol\beta_i^{\mathsf T}Q\boldsymbol\beta_i=E/3$ for all three basis vectors: the Rayleigh quotient on the unit sphere takes every value between its minimum and maximum, so choose the first vector with value $E/3$; the compression to its orthogonal complement has trace $2E/3$, so choose a second with value $E/3$ there; the trace identity gives the same value for the last vector. For $E>0$, taking $\boldsymbol\alpha_i=T\boldsymbol\beta_i/\sqrt{E/3}$ realizes $\sqrt E$; for $E=0$, every setting value is zero. Together with the upper estimate this identifies the frame supremum with $\sqrt E=\sqrt{\sum_i s_i^2}$. Flipping all Alice directions negates the real sum, so taking its absolute value does not change the supremum. This general equality is an argument, not a declaration in `result`.
- *Threshold sharpness and neighbouring questions.* If $c_B\ge2/3$, then $3(1-c_B)\le1$, so the first clause gives $\mathrm F_3\le1$. The second clause supplies a violating state at every nonnegative smaller centre length; a length cannot be negative. Thus the violation-supporting centre lengths are exactly $[0,2/3)$. This settles the threshold without determining the optimal value at each fixed centre length. That optimal envelope and closed formulas for one-sided hidden $\mathrm F_3$ remain unsettled here; the CHSH question is settled separately.
- *Effect on the source's Result 2.* For an invertible Alice filter, $E\mapsto f_A^\dagger E f_A$ bijects positive effect rays, and rescaling an effect does not change its normalized conditional Bob state. Hence the set of steered Bob states, and its ellipsoid centre, are unchanged, as in the source's lemma at lines 496–500; its invertible-filter convention is stated at line 341. Every normalized filtered state is a density matrix, so when $c_B\ge2/3$ all its resulting $\mathrm F_3$ values are at most one. The identity filter makes this value set nonempty, so its supremum is at most one: this is the corrected criterion $c_B\ge2/3\Rightarrow\mathrm{HF}_{3A}\le1$ when the source's optimization is read as a supremum. Exchanging the parties gives $c_A\ge2/3\Rightarrow\mathrm{HF}_{3B}\le1$, using the frame value's invariance under transposing $T$. These filtered quantities and implications, and attainment of filter optima, are not formalized by this module.
- *The decimal cutoff and examples.* The literal criterion with $c_B>0.66$ cannot be retained: for every $t\in(0.66,2/3)$ the existence clause supplies a state with $c_B=t$ and $\mathrm F_3>1$, and the identity Alice filter is admissible, so its one-sided optimized value is also above one. The paper's $\mathrm F_3$ regions certified solely by Result 2 must therefore use the exact centre condition $c_W\ge2/3$; no conclusion for the intervening strip follows from that criterion. An example also exhibiting hidden violation retains its inaccessibility conclusion whenever the appropriate centre condition meets this exact threshold. The hidden-violation calculations and the parameter regions in the source's figures are not certified here. The source's analytical-proof question for the $\mathrm F_3$ centre bound is answered in the registered sense; its further questions about optimizing hidden correlations and other dimensions or multipartite settings are outside the settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The APS-abstract reading, citation listings, Mukherjee–Paul reading and 40-abstract arXiv search are recorded in #26164 and were not independently reproduced. Xing–Yang's full text was not read; the issue records a publisher access barrier and no located arXiv version, so its abstract does not exclude an unobserved result in the full paper.

The frame/singular-value correspondence, the interpretation of the proof's mechanism, the threshold corollary, the filtering argument and the consequences for the source are arguments outside the type of `result`. The source's reported random-state experiment and the hidden-correlation calculations and plotted regions were not reproduced. The optimal fixed-centre envelope is open here, and the module supplies no formal definitions or theorems for hidden or one-sided-filter values, filter optimality, higher dimensions or multipartite extensions.

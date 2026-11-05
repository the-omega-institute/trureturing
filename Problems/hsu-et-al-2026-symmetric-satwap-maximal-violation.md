---
slug: hsu-et-al-2026-symmetric-satwap-maximal-violation
bibkey: hsuetal2026tradingsymmetry
doi: 10.1088/2058-9565/ae6bb1
url: https://arxiv.org/abs/2601.02893v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.result
---

# Identical TW measurements attain $2(d-1)$ for every $d\ge2$

## Problem

H.-Y. Hsu, G. N. M. Tabia, K.-S. Chen, M.-E. Liu, T. Vértesi, N. Brunner and Y.-C. Liang, *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*, arXiv:2601.02893v4; Quantum Science and Technology 11(3), 035003 (2026), conjecture following Eq. `Eq:symSATWAP`:

> Our computation results show that for the symmetric inequalities of~\cref{Eq:symSATWAP}, the measurement of \cref{Eq:CGLMP-Opt}, in conjunction with a symmetric maximally entangled two-qudit state, indeed reproduces the maximal quantum violation~\cite{SAT+17} of $2(d-1)$ for $d\le 100$. Together with the fact~\cite{Sarkar:2021aa} that this maximal quantum violation self-tests a maximally entangled two-qudit state,  we know that the symmetric family of SATWAP inequalities, \cref{Eq:symSATWAP}, also cannot exhibit a trade-off for $d\le 100$. Moreover, we conjecture that this holds true for any higher $d$ as well.

This quotation is from line 532 of the downloaded v4 TeX member `SymmetricBIV-arXiv_v2.tex` (2736 lines, md5 `6116dc142244f252c16a835d291626cf`). The symmetric-strategy definition is at lines 285–297, the measurements at lines 488–497, and the correlators and symmetric SATWAP expression at lines 513–530. See also [the literature note](../Library/Fourier/hsuetal2026tradingsymmetry.md).

The module uses computational indices $0,\ldots,d-1$ and real-exponent phases $\omega^t=e^{2\pi i t/d}$. Its measurement matrices are

$M_{a|0}=|a\rangle\langle a|$, $M_{a|1}=U|a\rangle\langle a|U^\dagger$, $U=TW$,

where $T=\operatorname{diag}(-1,1,\ldots,1)$ and $W_{ij}=1/[d\sin((i-j-1/2)\pi/d)]$. Both parties use this same measurement function. Module settings $0,1$ correspond respectively to settings $1,2$ in the source's symmetric SATWAP expression.

For a vector $\psi$, put $P_\psi(a,b|x,y)=\langle\psi|(M_{a|x}\otimes M_{b|y})|\psi\rangle$ and $C_{xy}^{(k)}=\sum_{a,b=0}^{d-1}\omega^{-k(a+b)}P_\psi(a,b|x,y)$. With $a_k=(1-i)\omega^{k/4}/2$, `satwapValue` is the complex-valued finite sum

$\tilde I_d(\psi)=\sum_{k=1}^{d-1}\left[\omega^{-2k}\left(a_k C_{00}^{(k)}+a_k^*C_{01}^{(k)}+a_k^*C_{10}^{(k)}\right)+\omega^{-3k}a_k C_{11}^{(k)}\right]$.

Issue [#22009](https://github.com/the-omega-institute/trureturing/issues/22009) fixes the attainment statement: for every natural $d\ge2$, there exists $\psi\in\mathbb C^d\otimes\mathbb C^d$ with $\|\psi\|=1$, $S\psi=\psi$, $\operatorname{Tr}_B|\psi\rangle\langle\psi|=I/d$, and $\tilde I_d(\psi)=2(d-1)$. This is proved. The universal quantum upper bound and the self-testing statement used by the source to infer minimal dimension are separate literature inputs.

## Motivation

The source compares the Hilbert-space dimension needed for maximal Bell violation with and without the requirement of a symmetric quantum strategy. Such a strategy uses identical measurements on a swap-invariant state. An attaining strategy in local dimension $d$ addresses the conjecture's existence question without increasing that dimension to impose symmetry. Combined with the source's cited quantum bound and self-testing result, it also gives the no-trade-off conclusion for this two-setting SATWAP family.

## Gap

The bounded literature check recorded in #22009 before any Lean reports:

- the published v4 TeX retains the explicit conjecture and its numerical range $d\le100$;
- Crossref and OpenAlex each list zero citing works;
- targeted searches for symmetric SATWAP strategies and author follow-ups find no settlement;
- searches of repository records, MathDB and formal-conjectures find no existing settlement; the two related preprints identified in the issue are reported to concern other settings without this construction.

`not-found-in-searched-scope`. These search readings are attributed to the preregistration; they are not an exhaustive literature claim.

## Route

Throughout, fix a natural $d\ge2$, settings $x,y\in\{0,1\}$, and outcome indices $a,b\in\{0,\ldots,d-1\}$. Write $\alpha_0=7/8$, $\alpha_1=11/8$ and $(V_x)_{ja}=\omega^{j(a+\alpha_x)}/\sqrt d$. All lemma names below refer to the module's private helpers.

1. **Fourier bases and the gauge identity.** For this $d\ge2$ and either setting $x$, `fourier_unitary` gives $V_x^\dagger V_x=I$. Put $D_{aa}=\omega^{a/2}$ and $F_{bb}=-i\omega^{-(b+1/2)/2}$. For $d\ge2$, `gauge_identity` proves $V_0^\dagger V_1=DWF$. In its proof, $q=\omega^{b-a+1/2}$ satisfies $q^d=-1$, so $q\ne1$; the geometric sum and the exponential formula for sine also establish that the sine denominator is nonzero.
2. **A common local transport and its state.** Put $L=TD^\dagger V_0^\dagger$. Given $V_0^\dagger V_0=I$, `transport_unitary` gives $LL^\dagger=I$. Define $\psi_{ij}=\sum_m L_{im}L_{jm}/\sqrt d$, the vector with coefficient matrix $LL^{\mathsf T}/\sqrt d$. `state_swap`, which has no extra hypothesis on $d$, gives its invariance under exchanging the indices. Given $LL^\dagger=I$, `state_reduced` gives reduced operator $I/d$. Given this reduced-operator identity and $d\ge2$, `state_norm` gives $\|\psi\|=1$.
3. **The measurement readout.** Put $B_0=I$, $B_1=TW$, $G_0=TD^\dagger$ and $G_1=F$. For $d\ge2$ and either setting $x$, `transport_readout` gives $B_x^\dagger L=G_xV_x^\dagger$. The diagonal entries of $G_x$ have modulus one by `setting_phase_norm`, for every natural $d$, setting $x$ and outcome $a$. For $d\ge2$ and the settings and outcomes above, `fourier_probability` consequently gives

   $P_\psi(a,b|x,y)=d^{-3}\left|\sum_{j=0}^{d-1}\omega^{-j(a+b+\alpha_x+\alpha_y)}\right|^2$.

4. **The correlator.** For $d\ge2$ and every integer $n$, `integer_sum` evaluates $\sum_a\omega^{an}$ as $d$ if $d\mid n$ and zero otherwise. For natural $k<d$ and real $s$, `wrapped_sum` evaluates the sum over pairs satisfying $d\mid j-l-k$ as $(d-k)\omega^{ks}+k\omega^{(k-d)s}$: there are $d-k$ unwrapped pairs and $k$ wrapped pairs. For $d\ge2$, settings $x,y\in\{0,1\}$ and natural $1\le k\le d-1$, `fourier_correlator` gives, with $s=\alpha_x+\alpha_y$,

   $C_{xy}^{(k)}=\omega^{ks}[(d-k)+k\omega^{-ds}]/d$.

5. **Exact cancellation.** For $d\ge2$ and either pair of settings, `offset_phase` gives $\omega^{-d(\alpha_x+\alpha_y)}=i$ for equal settings and $-i$ otherwise. For $d\ge2$, the proof of `satwap_sum` substitutes the correlators for each $1\le k\le d-1$. The phase exponents cancel by $-2k+k/4+7k/4=0$, $-2k-k/4+9k/4=0$ and $-3k+k/4+11k/4=0$. Each summand is exactly $2$, giving $\tilde I_d(\psi)=2(d-1)$. `result` uses this state and the preceding norm, swap and reduced-state identities to prove `claim`.

## Falsifier

An attainment identity for different measurements, setting labels or correlator phases would not answer the stated question. Here `twMatrix` is literally the source's $TW$ with the sine entries above; `measurement` uses the same matrices at both parties; `correlator` uses the two negative exponents; and `satwapValue` uses the coefficients of Eq. `Eq:symSATWAP` with the stated setting correspondence.

`reducedState` is the right partial trace of the rank-one operator of the same vector used in the Born quadratic form. The swap condition exchanges the two coordinate indices of that vector. Thus the four conditions concern one common state. `claim` asserts existence of that state for every $d\ge2$; it does not quantify over arbitrary measurements to assert a universal upper bound, nor assert a minimum-dimension or self-testing theorem.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.lean` (596 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.lean.json`, statement `sha256:d44ad5f596a963c2fa043281a439a5d76d7fa9c0196530e1515e52d44d592bf5`.

Declaration statements:

- `result`: `sha256:0e98ebe4c459e21de1a8a55fd9b293cde709fa7c5ce773c01f68645a58548601`;
- `claim`: `sha256:a31010d1777e2411a72f43cfddb034ee79bac5bdf9eadc9d900dd6e2ffd400e6`.

## Triage

Tier 1 conjecture of a 2026 journal article, preregistered in issue #22009 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $d\ge2$, there exists a vector in $\mathbb C^d\otimes\mathbb C^d$ of norm one, fixed by swapping its two factors, whose first reduced operator is $I/d$ and whose `satwapValue`, for the fixed identical measurements and phases defined above, equals the complex number $2(d-1)$.

**Computed, not formalized** (direct NumPy `complex128` evaluation):

- For the constructed family at $d=2,3,4,5,7,12,20,101$, no discrepancy above $10^{-8}$ was observed in the gauge identity, unitarity of $TW$, state normalization, swap symmetry, reduced state, probability normalization, correlator formula or value. The largest absolute value error was $8.70\cdot10^{-13}$; the largest correlator error was $7.45\cdot10^{-14}$. These are tests only of the listed dimensions.
- For $d=2,3,4,5,8$, diagonalizing the Bell matrices with the registered setting assignment gave largest eigenvalues $2,4,6,8,14$ to within $10^{-8}$. Reversing the assignment gave approximately $2.892130$, $4.385480$, $5.919091$, $10.576464$ for $d=3,4,5,8$; at $d=2$ both assignments gave $2$ to the same tolerance. No conclusion about the reversed assignment at untested dimensions is drawn.

**Argued, not formalized.**

- *The mechanism and its basis freedom.* Fix $d\ge2$, any attaining vector $\psi$ with the four stated properties, and any unitary $Q$ on $\mathbb C^d$. Replacing $\psi$ by $(Q\otimes Q)\psi$ and every measurement by $QM_{a|x}Q^\dagger$ preserves attainment: the unitaries cancel in each Born quadratic form; $S(Q\otimes Q)=(Q\otimes Q)S$ preserves vector symmetry; and the reduced operator becomes $Q(I/d)Q^\dagger=I/d$. Unitarity also preserves the norm. This common basis freedom explains how symmetry and maximal entanglement can survive a gauge change. It does not give attainment for an arbitrary new pair of fixed measurement bases.
- *Sharpness and the source's no-trade-off conclusion.* Hsu et al. (2026, arXiv:2601.02893v4, line 532) invoke the universal quantum bound from Salavrakos et al. (2017, Phys. Rev. Lett. 119, 040402, DOI 10.1103/PhysRevLett.119.040402), and the self-testing result from Sarkar et al. (2021, npj Quantum Information 7, 151, DOI 10.1038/s41534-021-00490-3). Conditional on those cited results applying to the source's relabelled expression, the attained value is the quantum maximum and the local dimension $d$ is minimal. Indeed, self-testing extracts a rank-$d$ maximally entangled state by local isometries; the reduced rank of that state tensored with any ancillary state is at least $d$, and local isometries preserve reduced rank. A local space of dimension below $d$ therefore cannot attain that value. The symmetric strategy already supplied in dimension $d$ consequently removes the symmetry-versus-dimension trade-off for every $d\ge2$, extending the range of the source's no-trade-off assertion at line 532.
- *Neighbouring questions.* The cancellation in `satwap_sum` for $d\ge2$ uses exactly two settings and the specified SATWAP coefficients. A construction for general numbers of settings, or an analogous attainment theorem for other Bell functionals, is open within this dossier. In particular, the source's CGLMP observations at line 508 are not settled: reusing the measurement matrices does not preserve the Bell functional, and changing its coefficients can change its maximizing state. The general analytic criterion requested at lines 985–986, and the source's examples of trade-offs for other inequalities, are not resolved by this attainment theorem.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation counts, targeted web searches, database searches and readings of the related preprints recorded in #22009 were not independently reproduced. The source's full numerical scan through $d=100$ was not reproduced; the independent finite tests are exactly those listed above.

The original proofs of the Salavrakos et al. upper bound and the Sarkar et al. self-testing theorem were not independently read or formalized here; their application to the relabelled expression remains a literature input to the conditional optimality and minimum-dimension conclusions. Everything labelled "Computed, not formalized" or "Argued, not formalized" is outside the formal statement of `result`. The extensions identified as open are not asserted to be globally unsolved in the literature.

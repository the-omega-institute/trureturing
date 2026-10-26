---
slug: van-herstraeten-guha-cerf-2024-phase-covariant-attenuator-coherent-refutation
bibkey: vanherstraeten2024nongaussian
doi: 10.1142/S0219749924400033
url: https://arxiv.org/abs/2312.15623v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result
---

# Van Herstraeten–Guha–Cerf Conjecture 2: coherent inputs for phase-covariant attenuators

## Problem

Conjecture 2 (Phase-covariant attenuator), section IV.B, arXiv:2312.15623v2, PDF p. 12, states: “The minimum output entropy of a phase-covariant attenuator channel ℳη,𝐩 is achieved by coherent states, ∀η,𝐩.” The domain is every transmissivity η in [0,1] and every probability vector p on the natural occupations. The assertion is that some complex coherent amplitude α minimizes the output entropy over all density operators on the full one-mode Fock space. Preregistration #11681 gives this quantifier order and the counterexample.

## Motivation

`D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result : ¬ claim` refutes the universal assertion using η=1/2, p=(7/8)δ₁+(1/8)δ₅, and the one-photon input. The model uses lp (fun _ : ℕ => ℂ) 2, with unrestricted states, amplitudes and environment support, a global two-mode beam-splitter unitary, and its square-root Kraus realization of the partial trace.

## Gap

The source supports Conjecture 2 by numerical minimization. The bounded literature check in #11681 found no settlement in the paper, Crossref, OpenAlex and the searched MathDB records; Semantic Scholar was rate-limited. This is not an exhaustive priority claim. The general equivalence of the basis-infimum entropy with spectral von Neumann entropy is literature-attested in the Wehrl note; the full Wehrl text has not been inspected and that infinite-dimensional equivalence is not kernel-proved here.

## Route

Totalness of the exponential family constructs the global displacements and beam splitter on the Hilbert completion. The beam splitter has the normalized binomial Fock action. A contraction-vector identity cancels the discarded-mode displacement, and summable rank-one ensembles establish coherent-output covariance for every probability vector. Fixed-total-occupation partial traces give the two finite output diagonals. Jensen row bounds and Parseval column sums identify their basis-infimum entropies with finite Shannon entropies. The settling proof transports all complete Hilbert bases to prove the required unitary invariance locally and certifies the strict logarithmic comparison.

## Falsifier

A mismatch between the source channel, state domain or entropy and their formal counterparts would invalidate source fidelity. Dropping coherent vectors, cutting off the ambient space, or restricting competing density operators would not settle the source assertion. A published prior settlement would change the bounded provenance conclusion. An argument for the conjecture at these parameters would contradict the formal counterexample under the stated correspondence.

## Evidence

The vacuum output has occupation probabilities (113,117,10,10,5,1)/256. The one-photon output has probabilities (115,8,117,0,5,8,3)/256. Every coherent input has the vacuum-output entropy. The exact certificate 115²·8¹⁶·3³=100507677308957491200>10²⁰, together with log(115)>log(113), gives strictly smaller entropy for the one-photon input. The chain and result are kernel-checked with only propext, Classical.choice and Quot.sound. The definition of entropy admits infinite values and arbitrary complete countable bases.

The published [settling Lean source](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.lean) contains this counterexample.

## Triage

Tier 1: an externally published conjecture whose preregistered bounded literature check found no settlement. The recorded resolution is Refuted for Conjecture 2, with no claim that the competitor is globally optimal.

### What the settlement shows

- **Proved in this module:** phase-invariant diagonal environments and displacement covariance do not suffice to make coherent inputs entropy minimizers. The explicit mixture of occupations 1 and 5 admits a lower-entropy one-photon input even though all coherent amplitudes share the same output entropy.
- **Proved in this chain and used in the module:** coherent-output covariance survives for every transmissivity in [0,1] and every probability vector. The failed step is the minimum-entropy conclusion, not that covariance identity.
- **Proved in this module:** for the pure occupation-1 environment at η=1/2, the vacuum and one-photon outputs are (1,1)/2 and (1,0,1)/2. These have the same nonzero spectrum; that equality supplies no universal minimization theorem for pure Fock environments.
- **Computed:** The exact witness distributions and integer certificate have the floating entropy values S(A)=1.0706928143706431 and S(B)=1.0629288654632991 nats, a gap of 0.007763948907343998. A finite numerical scan covers 504 floating comparisons for pure Fock environments, η in {0.1,…,0.9}, n in {0,…,7}, and m in {1,…,7}, with no violation beyond 10⁻¹²; probabilities below 10⁻¹⁵ are omitted in its entropy sum. This finite floating computation does not prove Conjecture 1.
- **Open:** Conjecture 1 for pure Fock environments, the global minimizer for this mixed environment, and a characterization of the diagonal environments admitting coherent minimizers. The source states the thermal geometric-distribution case as a known Gaussian optimizer result; that special case is literature-attested and not proved in this module.
- **Open in Lean:** the source's capacity bounds and Conjecture 3 on optimizer symmetries are not formalized here. This refutation does not settle Conjecture 3 because global minimality of the competitor is not asserted. Substitution of vacuum-output entropy for the minimum output entropy is invalid for this mixed channel. The source's capacity-bound statement with the actual minimum entropy is not refuted by this result, and its plots conditional on the separate pure-Fock Conjecture 1 are not settled by this mixed-environment counterexample.

### Retained pure one-photon components and their limits

The separate **Conjecture 1 (Fock attenuator)** asks whether coherent states minimize output entropy for every pure Fock environment occupation $n\in\mathbb N$, every transmissivity $\eta\in[0,1]$, and all density inputs on the completed one-mode Fock space $H=\ell^2(\mathbb N;\mathbb C)$. The [registered case n=1, η=1/2](https://github.com/the-omega-institute/trureturing/issues/17675#issuecomment-6209596574) still requires the actual output's extended spectral entropy to be at least $\log 2$ for every density input, with vacuum and every coherent input attaining equality. Both targets remain open. The inputs include arbitrary infinite support, arbitrary rank and singular operators; there is no energy, finite-entropy, purity or diagonality restriction.

The following three component arguments reuse published trace-class and beam-splitter results. Their retained source labels are `SpectralEntropyCap.operator_cap_entropy_lower`, `BalancedOnePhotonSector.balanced_one_photon_skew`, and `BalancedOnePhotonMinimumEntropy.densityReference` / `density_entropy_lower_of_half_bound`. These component sources remain unpublished, bind-only and at `admission_basis: none`; their scoped compilation establishes their exact statements, not admission or a formalized solution of either channel target. The [public scope and unfinished obligations](https://github.com/the-omega-institute/trureturing/issues/17675#issuecomment-6214013731) distinguish them from the published prerequisites linked below.

**A scalar cap bounds the actual extended spectral entropy.** Let $T$ be a native positive trace-class contraction on an arbitrary complete complex Hilbert space, with real part of its native trace equal to one. Assume the bound on this same operator,

$$
T\le cI,\qquad 0<c\le1.
$$

The published [`Reference` interface](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lean#L102) packages positivity, trace class and contraction; trace one and the $cI$ cap are additional hypotheses. Take the complete native spectral resolution $(e_i,\lambda_i)$, including the entire zero eigenspace, supplied by [`nativeResolution`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.lean#L168). Positivity gives $\lambda_i\ge0$. Evaluating the positive operator $cI-T$ on the unit eigenvector $e_i$ gives

$$
0\le\operatorname{Re}\langle e_i,(cI-T)e_i\rangle=c-\lambda_i,
$$

so every eigenvalue satisfies $\lambda_i\le c$. The diagonal of $T$ in this basis is exactly $\lambda_i$; [`diagonal_hasSum`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.lean#L37) and trace one therefore give the unconditional sum $\sum_i\lambda_i=1$.

For $\lambda_i>0$, logarithm monotonicity gives

$$
-\lambda_i\log\lambda_i\ \ge\ \lambda_i(-\log c).
$$

At $\lambda_i=0$, both sides are zero under the entropy convention $0\log0=0$. Since $-\log c\ge0$, the lower summands are nonnegative and summable, with sum $-\log c$. Sum the pointwise inequality in the extended nonnegative reals:

$$
\operatorname{ofReal}(-\log c)
=\sum_i\operatorname{ofReal}\bigl(\lambda_i(-\log c)\bigr)
\le\sum_i\operatorname{ofReal}(-\lambda_i\log\lambda_i)
=S_{\mathrm{spec}}(T).
$$

The last series is exactly the published [`spectralEntropy` definition](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy.lean#L238). Its sum may be $+\infty$, in which case the inequality still holds. The proof requires neither invertibility nor finite entropy, and it imposes no separability assumption on the Hilbert space. It uses the actual native spectrum throughout; it does not identify the dossier's basis-infimum entropy with spectral entropy.

**The balanced one-photon output is antisymmetric on the completed space.** The published [`BeamSplitter` source](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.lean#L203) fixes

$$
\operatorname{tensor}(v,w)(p)(q)=w(p)v(q),\qquad
(z_1,z_2)\longmapsto(tz_1-rz_2,rz_1+tz_2).
$$

Thus $e_{a,b}:=\operatorname{fockPair}(a,b)$ has coordinate
$e_{a,b}(p)(q)=\mathbf{1}_{p=b}\mathbf{1}_{q=a}$: the outer coordinate is the environment mode. At balance $t=r=\sqrt{1/2}$, the actual unitary $U=\operatorname{beamSplitter}(1/2)$ is the completed-space unitary, and the published [`beamUnitary_fock`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.lean#L411) identifies its occupation action with [`fockExpansion`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.lean#L402).

For every $m\ge0$, the existing one-photon calculation expands that exact occupation formula as

$$
\begin{aligned}
F^{t,t}_{m,1}
=\frac{t^{m+1}}{\sqrt{m!}}\sum_{i=0}^{m}\binom mi
\bigl(&\sqrt{i!}\sqrt{(m-i+1)!}\,e_{i,m-i+1}\\
&-\sqrt{(i+1)!}\sqrt{(m-i)!}\,e_{i+1,m-i}\bigr).
\end{aligned}
$$

Here $F^{t,t}_{m,1}$ denotes `fockExpansion t t m 1`; the finite algebraic identity holds for every real $t$. The two terms come from the environment indices $j=0,1$ in the published expansion. Their relative minus sign is the factor $(-r)^j$ for the one-photon environment. Exchanging the two coordinates sends $e_{a,b}$ to $e_{b,a}$. Reversing the finite index $i\mapsto m-i$, using $\binom m{m-i}=\binom mi$, exchanges the two bracket terms and leaves their factorial factors equal. Consequently

$$
F^{t,t}_{m,1}(p)(q)=-F^{t,t}_{m,1}(q)(p).
$$

The sign uses the stated phase convention and the odd parity of the environment photon; no parity restriction is placed on the system occupation $m$.

The extension to infinite support is part of the retained argument. The embedding $Jv=\operatorname{tensor}(v,|1\rangle)=\operatorname{lp.single}(2,1,v)$ is continuous and linear, as are $F=U\circ J$ and the coordinate evaluations $E_{p,q}(w)=w(p)(q)$. On every scalar occupation vector $z|m\rangle$, the published occupation action and the preceding identity give $E_{p,q}F=-E_{q,p}F$. Continuous linear-map extensionality on the Fock occupation vectors gives equality of these maps on all of $H$. Hence, for every completed Fock vector $v$, without a support or normalization restriction,

$$
\bigl(U\,\operatorname{tensor}(v,|1\rangle)\bigr)(p)(q)
=-\bigl(U\,\operatorname{tensor}(v,|1\rangle)\bigr)(q)(p).
$$

This establishes the full-space coordinate identity. It supplies no marginal operator estimate by itself.

**The native density adapter keeps the operator, and the half-cap stays a hypothesis.** The published [`Attenuator.DensityOperator`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.lean#L35) consists of a bounded positive operator $T$ with unconditional Fock-diagonal sum one. In the retained adapter, the complete Fock Hilbert basis is reindexed from $\mathbb N$ onto its range to meet the native set-indexed trace-class interface. Positivity identifies $|T|=T$, so the given summable diagonal supplies trace class. The published [`trace_eq_of_hilbertBasis` and summable trace-diagonal results](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal.lean) identify the native trace with that same diagonal sum; commuting the real-part map with the summable series gives real trace one. Finally, the published [`density_le_one`](https://github.com/the-omega-institute/trureturing/blob/a9337deba502d366c3bf1bc33adc7ea0fc5eb220/D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lean#L93) bounds the operator norm by the trace norm, which equals one for a positive normalized operator, and yields $T\le I$.

Accordingly `densityReference` packages exactly $T$, with no truncation, diagonal replacement or restriction on its support, rank, energy or entropy. Its `spectralEntropy` is the extended eigenvalue series of this original operator. If this same operator additionally satisfies $T\le I/2$, the scalar-cap argument with $c=1/2$ gives

$$
\operatorname{ofReal}(\log 2)\le
\operatorname{spectralEntropy}(\operatorname{densityReference}(\rho)).
$$

The adapter's automatic $T\le I$ only gives the $c=1$ bound. It does not provide the stronger half-cap assumed by `density_entropy_lower_of_half_bound`. In particular, substituting the actual density output $\sigma=\mathcal M_{1/2,1}(\rho)$ into this conditional result still leaves $\sigma.\mathrm{operator}\le I/2$ unproved; the notation does not supply that premise.

**The unresolved physical steps.** The actual channel in `Attenuator` uses the original columns $\sqrt{\rho}\,|m\rangle$, the beam splitter, and countable rank-one sums. What remains missing is the arbitrary-test-vector marginal operator estimate for completed antisymmetric outputs, followed by the unrestricted square-root-column ensemble and justified countable-sum argument identifying the bound with this same physical output operator. Vacuum spectral-entropy attainment and coherent attainment through actual covariance and native spectral-entropy unitary invariance also remain open in this chain. The finite vacuum/one-photon output equality recorded above establishes neither this all-input lower bound nor those native spectral-attainment bridges. These component arguments therefore do not settle the registered all-input $n=1,\eta=1/2$ case or the full all-$n$, all-transmissivity Conjecture 1.

### Conditional balanced Fock-two minimizer structure

The existing [Attenuator narrative](../Blueprint/D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.md) and [Entropy narrative](../Blueprint/D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.md) contain the complete conditional R1-R3 analytic argument. It concerns the actual balanced channel with the pure two-photon environment on completed complex Fock space. Assume the attained infimum of the actual output third elementary symmetric function is below $1/32$, together with the explicitly enumerated A1-A6 completed-channel compactness and variational prerequisites. Their full attainment proof is a separate exposition dependency; this addendum supplies none of its missing native joins. No initial photon moment, support, output rank or coefficient-phase restriction is imposed. These are prose arguments pending native formalization, not additional consequences certified by the existing frozen declarations.

R1 derives the actual complex trace-class Weyl multiplier, its two zero circles, continuity and injectivity, then uses both $h$ and $ih$ in the full second variation to prove simplicity of this self-consistent operator's top eigenvalue $\mu>7/32$ and an individual positive gap. R2 derives the repository-sign environmental transfer for every bounded output operator, obtains real operator-norm smoothness from the finite Fock environment, and uses an isolated finite-rank Riesz range and finite smooth seeds before differentiating the unknown eigenvector. Its exact pure Wirtinger coefficient and Parseval identity prove every rising-factorial photon moment and every number-operator domain. R3 constructs the actual real horizontal Hessian using the restricted real adjoint, legitimate S1/S2 trace products and a compact correction. It proves nonnegative Fredholm index zero and coercivity off the entire finite-dimensional kernel, distinguishes the full sphere's phase direction, and retains the exact factor two between the Taylor coefficient and the constrained Hessian. The owner narratives give all proofs, qualifications C1-C6 and citation limits.

The physical source conventions are available in the immutable published [BeamSplitter](https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.lean), [completed displacement covariance](https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.lean) and [actual attenuator](https://github.com/the-omega-institute/trureturing/blob/bc0d5339476df8b41d58d7cde040a82266a9f416/D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.lean) sources. Those sources establish their own stated interfaces; they do not kernel-verify the new Weyl-uniqueness, smooth spectral-range, moment or real-Hessian arguments. KLSW's classical Weyl theory, localization eigenfunction regularity, He's purity/coherent-equality results, Ramos's profile methods and Frank-Nicola-Tilli's Husimi bounds retain their distinct scopes as described in the narratives; no priority or novelty claim is made.

The same-input cubic estimate, all middle relative sectors, the full high-degree tail and every center coefficient remain unresolved. A smooth simple self-consistent eigenvector with nonnegative Fredholm Hessian has not been excluded. No classification of minimizers or of the whole Hessian kernel follows, and no negative physical input is constructed. The unrestricted balanced two-photon entropy inequality, countable spectral/ENNReal entropy bridge, and original all-$n$/all-$\eta$ Conjecture 1 remain open. The one-photon and mixed-environment statements elsewhere in this dossier keep their original hypotheses and evidence boundaries.

## ASSUMED-UNVERIFIED

Citation-index completeness, exhaustive worldwide novelty, the sentence-by-sentence journal/arXiv correspondence, and the general infinite-dimensional spectral entropy equivalence are not kernel-verified. Wehrl's full text has not been inspected. The standard axiom boundary and the exact source/model correspondence remain distinct from these bibliographic boundaries. CLAUDE.md §3.9 requires a faithful same-delivery registration attempt for selected new public theorems, with an honest linked-issue disclosure when registration is unfinished. The retained scalar-cap, balanced-sector and conditional density-floor component audits remain unfinished under [#17675](https://github.com/the-omega-institute/trureturing/issues/17675#issuecomment-6214013731): source reconstruction, lawful enrolled readout and actual-law bridge, whole-family variation and sensitivity, observational dependence, compiled Reg proofs and current binding evidence are missing. This existing-result prose creates no new audit target and completes none of those audits; the linked issue supplies neither admission nor registration evidence.

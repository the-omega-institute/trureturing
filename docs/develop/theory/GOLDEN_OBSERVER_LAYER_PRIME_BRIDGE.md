# Golden observer, layer, prime, and phase bridge

Status: research synthesis. Lean declarations are the truth source. This note separates proved library structure from geometric interpretation and open bridges.

## 1. Working picture

The discussion starts from a carrier with hidden coordinates and a family of observer readouts. A cut-and-project construction is one important source of readouts. The abstract observer theory does not require every readout to arise from a geometric projection.

Four notions must remain distinct:

- a projection or postprocessing map can hide information;
- a refinement adds information and shrinks observation fibers;
- symmetry breaking occurs when two states that were previously observationally identical become distinguishable;
- observation time is the first readout depth at which this distinction appears.

A projection layer is therefore not automatically a breaking event. Breaking is relative to a pair of hidden states and a chosen observer family.

The claim that the physical carrier is specifically six-dimensional, or that physical time is literally motion through a projection tower, remains an open model premise. No theorem in this lane assumes either claim.

## 2. Frequency is a mode of variation

The existing Fourier-fiber library supplies a finite model. Hidden amplitudes are transported by modal multipliers, and a scalar observation at time `t` is a superposition of terms of the form

```text
amplitude_j * multiplier_j^t.
```

Several hidden components may therefore contribute to one observation. Frequency belongs to their variation law along an orbit or scale path. It is not identical to a layer index.

Existing finite spectral tomography proves that sufficiently many temporal samples recover finitely many distinct modes. Existing temporal-fiber results prove that adding observations can only shrink the hidden fiber.

This supports the interpretation:

> an observation may be a superposition of hidden projected components; frequency describes how those components vary; a time window separates modes by accumulating readouts.

It does not prove that every geometric projection layer is one pure Fourier mode, nor that Fourier analysis creates physical time.

## 3. Observation time as a fiber boundary

`D5/S3/ObserverMemory/FourierFibers/ObservationTime.lean`

reuses the repository's canonical future-readout and separation-time definitions. For an eventually separated pair:

- every readout before `separationTime` agrees;
- the readout at `separationTime` differs;
- the pair belongs to the finite observation fiber exactly for horizons below that boundary.

Thus observation time is a first-visible depth:

```text
same fiber -> first visible difference -> excluded from every deeper fiber.
```

Dynamical time counts updates. Observation time is the least update depth required by a particular observer to expose a particular hidden difference.

## 4. Zeckendorf as the address of golden depth

The frozen library proves that every natural layer has a canonical Zeckendorf representation, that decoding recovers the layer, and that its least occupied Fibonacci index controls the golden Euler beta ledger.

The merged and frozen theorem

```text
D5.S3.Analytic.GoldenEulerBetaZeckendorf
  .golden_euler_beta_zeckendorf
```

proves that

```text
beta(v + 1) - beta(v)
```

is `phi^2` when the least Zeckendorf index of `v + 1` is even and `phi` when it is odd.

The adapter

`D5/S3/Analytic/EulerGerm/ZeckendorfGoldenBetaGapBridge.lean`

connects the equivalent least-digit criterion used by the golden mechanical word:

- least digit absent selects the long `phi^2` step;
- least digit present selects the short `phi` step.

Zeckendorf is therefore a lossless address and transition code for golden depth. The phrase "discrete DNA" refers to this address-and-grammar role. It does not encode prime identity, continuous phase, modal amplitude, the scale lift, or every orientation coordinate.

## 5. The golden gap word is deterministic and constrained

`D5/S3/Analytic/GoldenEulerGapWordConstraints.lean`

uses the existing golden-word identification and desubstitution theorems to prove more than a two-value dichotomy:

- a true golden letter gives a long `phi^2 log p` frequency gap;
- a false golden letter gives a short `phi log p` frequency gap;
- two consecutive short gaps never occur;
- three consecutive long gaps never occur.

The same forbidden-word laws are transported to the Euler phase alphabet.

This is the rigorous deterministic content behind the phrase "not an independent Bernoulli step law." The repository has not yet chosen a probability measure on the orbit and proved a formal non-iid theorem. What is already proved is stronger at the symbolic-language level: the generated word belongs to a constrained Fibonacci/Sturmian language rather than the unrestricted binary full shift.

## 6. Odd breaking and even completion

`D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion.lean`

abstracts the exact content of odd breaking and even completion. If each update applies an involution to a chosen readout, then:

- every odd iterate places that readout on its flipped sheet;
- every even iterate restores the original readout;
- if the initial readout is not fixed by the involution, every odd iterate is visibly different;
- restoration of the readout does not imply return of the full hidden state.

`D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.lean`

instantiates this law on golden-helix orientation. Two steps restore orientation while the lifted level has advanced.

The valid phrase is therefore:

> odd breaking and even completion of an involutive readout.

A universal parity law for every projection coordinate would require an involution on every proposed layer and remains open.

## 7. Prime locality and golden depth are transverse coordinates

`D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.lean`

formalizes a carrier `Local x Layer`. It proves:

- a fixed local fiber and fixed layer fiber meet in one state;
- a local-only move commutes with a layer-only move;
- each coordinate observer is blind to motion in the other coordinate;
- the paired observer is faithful.

This is the precise present meaning of transverse. No inner product or angle has been defined, so Hilbert-space orthogonality is not claimed.

`D5/S3/Analytic/EulerGerm/PrimeZeckendorfCoordinates.lean`

specializes the product carrier to

```text
prime channel x golden layer.
```

It proves that `(prime, Zeckendorf(layer))` is a lossless address for `(p,v)` and rewrites each local golden factor as a sum over Zeckendorf-addressed layers inside one fixed prime channel.

## 8. Prime-scaled golden frequency

`D5/S3/Analytic/EulerGerm/PrimeZeckendorfFrequencyBridge.lean`

defines

```text
omega(p,v) = beta(v) * log(p).
```

The exact consecutive increment is

```text
least digit absent  -> phi^2 * log(p)
least digit present -> phi   * log(p).
```

Every prime channel therefore carries the same deterministic golden long-short word at its own logarithmic scale.

The cross-prime balance theorem states

```text
log(q) * delta omega_p(v) = log(p) * delta omega_q(v).
```

The frozen excited heat spectrum omits the vacuum, so spectral index `k` corresponds to golden layer `v = k + 1`. Its first mode is

```text
omega_1(p) = phi^2 * log(p).
```

## 9. Anonymous prime labels and calibrated prime rigidity

`D5/S3/Analytic/EulerGerm/PrimeRelabelingUnderdetermination.lean`

proves an obstruction. Golden depth and abstract product geometry are invariant under arbitrary permutations of the prime-label type. They cannot select the arithmetic meaning of a prime coordinate by themselves.

`D5/S3/Analytic/EulerGerm/PrimeZeckendorfFrequencyRigidity.lean`

adds the calibrated first frequency `phi^2 log p` and proves:

- equality of first frequencies forces equality of prime channels;
- first frequency plus Zeckendorf address faithfully recovers `(p,v)`;
- a prime relabeling preserving all first frequencies is the identity;
- the first-frequency family is linearly independent over the rationals, by rational independence of prime logarithms.

Thus the gap is narrower than "why do primes appear?"

1. anonymous golden geometry does not canonically label prime channels;
2. the numerical scale `log p` does canonically distinguish them;
3. a geometric bridge must therefore derive normalized valuation, absolute-value, norm, or spectral data equivalent to this scale.

## 10. Finite prime places and the Archimedean scale

`D5/S3/Factorization/Embeddings/PrimeArchimedeanGoldenFrequencyBridge.lean`

connects the frequency calibration to existing rational p-adic truth sources. For prime targets `p` and finite prime places `q`:

```text
|p|_p = 1/p
|p|_q = 1 when q != p.
```

Consequently the target prime has one nontrivial finite-place coordinate. At its own place,

```text
p * |p|_p = 1.
```

The infinite-place logarithmic scale is `log p`, and the first golden frequency is its golden modulation:

```text
omega_1(p) = phi^2 * log(p).
```

This supplies the current arithmetic explanation:

> prime identity is the support location of a valuation profile; `log p` is the continuous Archimedean magnitude paired with that finite place; golden depth modulates the magnitude.

It still does not derive the valuation profile from a cut-and-project carrier.

## 11. Euler temporalization produces a two-letter phase alphabet

`D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw.lean`

maps a real angle to the unit circle:

```text
U(theta) = exp(i theta) = cos(theta) + i sin(theta).
```

The two deterministic prime-local frequency letters are

```text
short(p) = phi   * log(p)
long(p)  = phi^2 * log(p).
```

At time `t`, they become two phase letters:

```text
U_short(p,t) = exp(i t phi log p)
U_long(p,t)  = exp(i t phi^2 log p).
```

Because `phi^2 = phi + 1`, the long phase factors exactly as

```text
U_long(p,t) = U_short(p,t) * exp(i t log p).
```

Thus a long step consists of the short golden rotation together with one additional ordinary prime-log rotation.

The least Zeckendorf digit chooses one of these two phase letters at every layer. The forbidden short-short and long-long-long words remain valid before aggregation.

## 12. Scalar phase endpoints forget chronology

The same Euler-phase module proves

```text
U_short * U_long = U_long * U_short.
```

A scalar `U(1)` endpoint therefore records the accumulated angle while forgetting whether the path was short-then-long or long-then-short.

This is a formal obstruction to recovering time order from one terminal scalar phase. Recovering chronology requires at least one of:

- time-resolved intermediate readouts;
- an ordered word or path signature;
- matrix- or operator-valued transport;
- a noncommutative group;
- Magnus, Chen, or Hopf-signature data.

The repository's chronological-signature and second-Magnus lanes are natural owners of this missing order information.

## 13. Real and imaginary parts have different observer roles

`D5/S3/ObserverMemory/FourierFibers/PrimeZeckendorfTemporalization.lean`

first distinguishes two temporalizations of the same frequency:

```text
heat:  exp(-t omega)
phase: exp(i t omega).
```

Positive heat time remains injective in the prime channel. Finite collections of phase channels have arbitrarily late near-recurrence.

`D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode.lean`

combines them into

```text
M_p(sigma,t)
  = exp(-sigma omega_1(p)) * exp(i t omega_1(p)).
```

Euler decomposition gives

```text
M_p(sigma,t)
  = exp(-sigma omega_1(p))
      * (cos(t omega_1(p)) + i sin(t omega_1(p))).
```

The norm depends only on `sigma`:

```text
|M_p(sigma,t)| = exp(-sigma omega_1(p)).
```

For `sigma > 0`, the norm identifies the prime channel. On the imaginary axis `sigma = 0`, every norm equals one and only wrapped phase remains. Finite prime phase vectors can return arbitrarily close to coherence at arbitrarily late times.

The correct observer interpretation is:

```text
real parameter      -> amplitude, scale, dissipation, prime identity
imaginary parameter -> angle, rotation, interference, recurrence.
```

This does not identify either parameter with laboratory time.

## 14. Where zeta enters

For each prime `p`, the frozen golden Euler germ sums all golden layers in that local channel. The global construction then multiplies the local towers over all primes.

The frozen `GoldenGermZetaFactorization` theorem factors the result through

```text
riemannZeta(phi^2 * s)
```

times a normalized higher-layer correction. The common first frequency `phi^2 log p` supplies the zeta skeleton. Higher golden layers retain the deterministic Sturmian and Zeckendorf grammar.

The two assembly directions are:

```text
inside one prime: sum over golden depth
across primes:    multiply local towers by the Euler product.
```

Zeckendorf and zeta are transverse in role and coupled in generation. Zeckendorf organizes depth inside each local factor. Zeta appears after the common local mode is aggregated across prime channels.

## 15. Diagonal paths

A diagonal is naturally a path on a product carrier in which local and layer coordinates change together. The current library proves the uncoupled product geometry and the separable frequency law `beta(v) log p`. It does not yet supply a canonical diagonal update.

Any proposed diagonal must specify:

- the update on prime or local coordinates;
- the update on golden or Zeckendorf depth;
- the coupling relation;
- the observer that distinguishes the path;
- the chronology data retained after projection;
- whether parity completion concerns one readout or the full state.

No diagonal here is identified with the Riemann critical line.

## 16. Central open bridge

The hard missing theorem is now:

> construct a canonical map from a genuine golden cut-and-project or completion carrier to normalized valuation or absolute-value data, prove coverage of prime places, and prove rigidity against prime relabeling.

The repository already has the target arithmetic behavior:

```text
geometric carrier
    ?
valuation support -> prime place
infinite magnitude -> log p
golden depth       -> beta(v)
frequency          -> beta(v) log p
Euler phase        -> exp(i t beta(v) log p).
```

A candidate map must prove existence, coverage, normalization, and relabeling rigidity. Merely attaching prime names to anonymous channels does not close the bridge.

## 17. Verification boundary

The branch contains candidate Lean and matching Scribe sources for observation time, involutive parity, product transversality, prime-Zeckendorf coordinates, prime-frequency rigidity, finite-place calibration, Euler phase letters, forbidden words, and real-imaginary mode separation.

GitHub admission is the compilation authority. No new declaration in this PR is described as kernel-closed until engineering checks, canonical Lean report production, mathematical content checks, and protected admission all succeed.

## 18. Append-only provenance and status correction, 2026-09-05

Sections 1-17 preserve the archived theory input from PR #5014 at commit `ca56026e654399bb365ad813f290f70dd2864538`, blob `70a4c91387bcc3ecba71a4ca1f900cf837307924`. They are historical research prose, not a substitute for the current Lean registry or proof reports. In particular, historical uses of "proves" refer to proposed source or to the separately identified frozen owner; prose alone cannot certify a new declaration.

PR #5014 is closed, unmerged and superseded. Its decomposition comment identifies eight landing PRs: #5318, #5412, #5425, #5435, #5457, #5473, #5507 and #5544. Twenty-four modules were landed. This does not imply that every later file in the archived omnibus branch was landed. The three binomial/Parikh candidate modules were absent from the pinned dev `611c3bf36cfc0fd83727c6b5657d78ec8e0917eb` and are recovered in #5567 under sibling buckets:

```text
D5/S1/Words/GoldenRecovery/
D5/S3/Observer/GoldenChronology/
```

The already frozen step-two chronology, factor complexity, golden balance and palindromic complexity owners are imported without modification. This theory restoration is a separate data-only change. The attached `GoldenFactorHeisenbergReadout` implementation is not duplicated; its mathematical target is represented by the single binary Parikh owner and a thin golden-language adapter.

Implementation provenance: GPT-6 Pro main session, no specialist execution skill and no independent model review. Three local exact-integer worker processes tested separate claims concurrently. Remote GitHub compilation is independent of those self-checks. New #5567 declarations remain candidates unless their source-bound reports establish otherwise.

## 19. The legal language changes the observation problem

The unrestricted event-word witness `ABBA/BAAB` establishes a genuine second-order collision that a third-order representation can resolve. Those two words cannot both be consecutive golden long/short factors: whichever letter is short, one word contains two adjacent short steps.

Let `W_n` be the entire set of length-n consecutive factors of the fixed golden word, identifying equal word contents at different starts. This differs from a space of absolute occurrence indices and from the unrestricted binary full shift.

For a binary word w define

```text
r(w) = number of long/true letters
z(w) = number of short/false letters
P(w) = number of scattered long-before-short pairs
m(w) = 2 P(w) - r(w) z(w).
```

Here a scattered pair need not be adjacent. The standard ordered Parikh product is

```text
T(w) = product over letters of (I + E01) or (I + E12)
     = [[1, r(w), P(w)], [0, 1, z(w)], [0, 0, 1]].
```

Its existing factorial Chen signature has degree-one entries r and z and doubled degree-two center 2P. The existing doubled Magnus coordinate has center m. This connects the combinatorial statistic to an actual fixed noncommutative observer, rather than appending a new statistic to an unrelated theorem.

Classical attribution remains explicit. The Parikh matrix mapping is from Mateescu, A. Salomaa, K. Salomaa and Yu, RAIRO ITA 35(6) (2001), 551-564, DOI 10.1051/ita:2001131. Rigo and Salimov, TCS 601 (2015), 47-57, DOI 10.1016/j.tcs.2015.07.025, established the general Sturmian second-order binomial faithfulness phenomenon. The repository contribution is the explicit representation and kernel interface; no priority claim is made for those classical results.

## 20. New deduction: window parity controls center-only recovery

The candidate `GoldenMagnusParityRecovery.center_recovers_fixed_length_iff_even` states:

```text
m restricted to W_n is injective  iff  n is even.
```

The proof explains why.

At one fixed length, golden balance gives `abs(r-s) <= 1` for the true counts of any two factors. Equal centers imply

```text
2P - r(n-r) = 2Q - s(n-s).
```

If `s=r+1`, this simplifies to

```text
2P - 2Q = 2r + 1 - n.
```

For even n, the right side is odd and the left side is even. Therefore adjacent different counts cannot have equal centers. Counts agree, pair counts agree, and the already recovered binomial theorem yields the same full factor.

For every odd n the frozen palindromic-factor complexity theorem gives two distinct legal palindromes. Reversal exchanges the two orientations of unlike-letter pairs, so

```text
m(reverse(w)) = -m(w).
```

Each palindrome has m=0. Thus the two distinct legal palindromes certify a collision at every odd length.

A further candidate theorem bounds each fixed-length central fiber by two distinct word contents. Golden balance permits at most two true counts, and each count together with the center recovers one word.

This is a parity law for observation-window length. It is not an identification of window parity with prime-factor parity, Zeckendorf least-index parity, an involutive update count, or homogeneous Lie degree. At length one the center is constant and count alone suffices; odd length must not be summarized as "both coordinates are always indispensable."

## 21. Intrinsic information replaces theorem-count narratives

The normative reference is `docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md`, v4.3. Its sections 5.7-5.10 distinguish flat leave-one-out exclusive capture, overlapping capture, ordered layered capture, and generated-kernel closure. Section 6.1 separates general structural inclusion from the implemented finite engine.

For one fixed state object X and one complete peer family, write

```text
K_S = agreement kernel of the selected readouts
D_X = {(x,y) | x != y}
E_S = K_S intersect D_X
U_i = E_(I without i) minus E_I.
```

Finite exact rates use only `|D_X| = |X|(|X|-1)`. There are no arbitrary importance weights, historical baselines, user-tuned thresholds or external numerical judges.

This changes how the present research is accounted for. A full Parikh matrix, its first-degree counts and its Magnus center are not three independent information gains. If all three are peers, the full matrix determines the other two, while the other two jointly determine the full matrix on the legal object. Every peer then has zero unique capture. This observation does not invalidate any of the mathematical identities; it identifies semantic redundancy in that particular catalog.

Increasing signature degree similarly describes an ordered refinement chain. Its per-layer gains must be treated as ordered layered capture. They cannot be reported as all-positive flat exclusive captures when stronger cumulative observers remain in the same peer family.

## 22. Complete four-state arena and exact kernel diamond

The first explicit intrinsic calculation uses the entire length-three factor object. The four words are

```text
SLS, SLL, LSL, LLS.
```

They occur at starts 4, 1, 0 and 2. The frozen factor-complexity theorem proves there are exactly four length-three factors; thus their word-preserving finite presentation is complete. No sampling cutoff defines the arena.

The actual readouts are:

| Word | (r,z) | P | m |
|---|---|---:|---:|
| SLS | (1,2) | 1 | 0 |
| SLL | (2,1) | 0 | -2 |
| LSL | (2,1) | 1 | 0 |
| LLS | (2,1) | 2 | 2 |

There are twelve ordered distinct pairs. In the explicitly named two-coordinate analysis view, the residual counts are

```text
no readout       12
count only        6
center only       2
count and center  0.
```

The exclusive capture counts are two for count and six for center, with exact rates 1/6 and 1/2. The kernels are incomparable: SLL and LLS agree in count but differ in center; SLS and LSL agree in center but differ in count.

The generated kernel closure is the four-node diamond consisting of universal agreement, count agreement, center agreement and identity. Either coordinate can be added first. The two ordered capture decompositions are 6+6 and 10+2; both terminate with all twelve distinct pairs separated. The flat unique counts 2 and 6 sum to eight because four pairs are captured by both individual observers. Overlap is not itself a redundancy verdict.

A second analysis view explicitly retains the full matrix as a third peer. Joint residual remains zero, but all three exclusive capture counts become zero. This is the candidate `full_presentation_faithful_but_not_irredundant` theorem.

## 23. What is compiled, and what remains an implementation obligation

The candidate `GoldenLengthThreeCapture` imports the existing `PrimitiveLawArena`, `NativeTheoremUnit`, `Catalog` and `ExactRate` owners. Each unit has a nonconstant object law of its typed CUT realization. It does not use `Statement := True` to attach an arbitrary observer. The finite equations are Lean propositions proved by ordinary `decide` reflection in the same build that checks the source theorems.

Both catalogs are explicitly analysis views. No designated system root is sealed by this batch, and the positive two-coordinate view cannot certify a maximal catalog that also contains the matrix peer. No singleton arena is cloned to hide redundant peers. The finite presentation has a proved word-preserving equivalence and readout transport to the full factor subtype.

The v4.3 normative structural-arena/disposition layer is not fabricated where no executable owner was found on the pinned base. Full automatic registration, maximal-root reconciliation and disposition emission remain separately scoped engine-integration obligations. This volume never treats local finite tests or a PR's existence as completion of those obligations.

Scribe mirrors provide source-linked commentary. The exact theorem statements are owned by Lean; this batch does not synthesize raw statement-v1 fixtures by hand and does not weaken missing-source failures.

## 24. Executed parallel checks and remaining research order

Three local processes ran distinct exact-integer checks concurrently before the remote write:

1. 327,680 golden windows, lengths 1-80 with 4,096 starts each, checked the parity classification prediction and representation identities.
2. All 8,191 binary words of lengths 0-12 checked the generic reversal/pair identities.
3. Exact pair-collision calculations for the observed complete factor collections at lengths 1-6 checked the proposed finite rates and redundant-peer behavior.

These are reproducibility checks only. Universal truth and formal status come from the Lean kernel and repository admission. #5567 is the corresponding new source PR, based on dev rather than the closed omnibus branch.

The next logical work is to transport the proved parity-minimal kernels into the designated-root analysis/disposition machinery once its current executable interface is verified, preserving zero-gain findings. A further generalization can replace the golden slope by a fixed irrational mechanical slope, but must first reuse existing mechanical-word owners and retain the finite-language restriction. The geometric-to-valuation bridge in section 16 remains open and is not closed by the observer classification.

## 25. Literature-grounded continuous displacement readout, 2026-09-06

The next source batch is PR #5750, stacked on the still-candidate #5567 rather than pretending its golden-recovery dependencies are frozen. It adds four Lean modules with matching authored Scribe under `D5/S3/Quantum/WeylChronology/`. Repository search on dev `315d6cb58b0c62155e313b59d4236cbd854b5dc5` found the frozen finite ZMod Weyl family in `Quantum/Algebra`; that representation is retained and is not substituted for arbitrary real translations.

Three primary references determine the adopted model and readout:

1. C. Fluehmann and J. P. Home, Direct characteristic-function tomography of quantum states of the trapped-ion motional oscillator, Physical Review Letters 125, 043602 (2020), DOI `10.1103/PhysRevLett.125.043602`, arXiv `1907.06478`. The full PDF and its readout-circuit/equation page were inspected. Spin-dependent displacement followed by phase-selective electronic readout gives real and imaginary characteristic-function components. This is an experimental precedent for the readout mechanism, not an experiment with our golden words.
2. A. C. Vutha et al., Displacement operators: the classical face of their quantum phase, arXiv `1702.01833`. This supplies classical/quantum displacement-phase context; Weyl composition is not claimed as a discovery of this project.
3. N. Razian, E.-J. Chang and H.-K. Lau, Discrete-variable assisted error correction of continuous-variable quantum information, arXiv `2604.06565v1`, 8 April 2026. The full HTML, equations (4)-(5), and the coupling/alias discussion were inspected. This is a theoretical preprint using a DV ancilla to read CV displacement information. It does not validate our protocol experimentally or confer its QEC claims on this batch.

The controlled encoding is L -> D(a,0), S -> D(0,b). Golden grammar constrains event order. The two quadrature directions and amplitudes are chosen laboratory controls; they are not derived from golden geometry or prime arithmetic. No physical specialness of an amplitude ratio phi is assumed.

## 26. Concrete wavefunction representation and chronology phase

In dimensionless quadratures with commutator convention [Q,P]=i/2, define the actual function action

```text
D(x,y) f(q) = exp(i*(2*y*q-x*y)) f(q-x).
```

`SchrodingerDisplacement.displacement_comp` derives directly

```text
D(x,y) D(u,v) = exp(i*(y*u-x*v)) D(x+u,y+v).
```

The left operator acts last. The inverse, scalar-phase equivariance and pointwise intensity transport are also derived. No assumed CCR, BCH axiom or finite Fock truncation is used. The formal carrier is functions R -> C. Completion to a strongly continuous unitary L2 representation and self-adjoint generator domains are not claimed.

Executing a list with its head first gives the exact normal form

```text
U_w f = exp(i*a*b*m(w)) D(a*r(w), b*z(w)) f.
```

This imports the existing integer `magnusCenter`; no independent chronology counter is introduced. Reversal preserves r,z and negates m, hence

```text
U_w f = exp(i*2*a*b*m(w)) U_reverse(w) f.
```

Bare pointwise intensities are identical. With a reference arm and analyzer theta, recombination yields

```text
plusOutput = (1+exp(i*(2abm-theta)))/2 * referenceWavefunction.
```

The candidate `normalized_output_probability` integrates the squared modulus and obtains `(1+cos(2abm-theta))/2` for a unit-normalized reference. This exposes a state-independent relative phase. The factor two belongs to word/reversal comparison, not to a single word versus its net displacement.

## 27. Count-only compensation removes the need to replay the reverse

Reversal comparison is useful for calibration but requires controlled access to both histories. A more operational reference uses only their inventory:

```text
D(-ar,-bz) U_w f = exp(i*ab*m(w)) f.
```

`endpoint_compensated_word_phase` proves that this compensation restores the input wavefunction up to the chronology phase. The compensator depends on counts, not their ordering. Interfering the compensated branch with an unchanged coherent reference yields

```text
p_theta(w) = (1+cos(ab*m(w)-theta))/2.
```

`normalized_compensated_probability` needs only unit normalization of the input; it does not assume a Gaussian, coherent, squeezed or Fock input shape. `compensated_probability_eq_chronology_fringe` connects this actual device to the calibrated recovery owner with kappa=ab/2.

A physical ancilla realization requires coherent controlled execution of the signal and reference branches. A global phase of an uncontrolled black-box channel does not become measurable merely by writing a control symbol. The protocol is suitable as a candidate diagnostic for repeatable control histories with known inventory; it is not a reconstruction procedure for an arbitrary unreplayable past. The ideal motional state is restored, but finite control error and ancilla backaction are not modeled.

## 28. Exact readout kernels, calibrated range and example

The Ramsey amplitude is `(1+exp(i*(phase-theta)))/2`. The two settings theta=0 and theta=pi/2 give `(1+cos phase)/2` and `(1+sin phase)/2`. `quadrature_readout_kernel` identifies their joint kernel exactly with the wrapped complex phase. The zero setting loses orientation, and the two-setting readout still aliases phase zero with phase 2pi.

For every binary word of length n, the oriented-pair identity gives

```text
abs(m) <= r*z,        4*abs(m) <= n^2.
```

Thus kappa != 0 and `abs(kappa)*n^2 <= pi` place `2*kappa*m` inside the monotone sine band. The ideal pi/2 fringe then has exactly the same kernel as m. A sufficient explicit choice is

```text
safeCoupling(n) = pi / (2*(n+1)^2).
```

For reversal comparison set ab=safeCoupling(n). For endpoint compensation set ab=2*safeCoupling(n). Both realize the same calibrated fringe. The latter still requires counts to construct the compensation, even where the resulting ideal probability identifies counts mathematically. Observation sufficiency does not eliminate state-preparation resources.

At length four, this choice predicts:

| Factor | m | Ideal plus probability |
|---|---:|---:|
| SLSL | -2 | 0.37565506 |
| LSLL | -1 | 0.43733338 |
| SLLS | 0 | 0.50000000 |
| LLSL | 1 | 0.56266662 |
| LSLS | 2 | 0.62434494 |

These are model values, not experimental data. The source adapters recover a same-length legal golden factor from count plus calibrated fringe, or from fringe alone at even length using the parent parity theorem. At each odd length two distinct legal factors remain equal for every coupling; that collision is retained. Only the implication palindrome -> balanced fringe is imported in this batch. The earlier full zero-center iff palindrome argument is not silently treated as a compiled dependency.

## 29. Scientific and verification boundaries of the Weyl batch

The formal result is a concrete representation and recovery chain, not a new discovery of Weyl interference:

```text
existing golden Magnus integer
 -> concrete ordered wavefunction action
 -> a reference or count-only compensation
 -> integrated two-port probability
 -> an explicit calibrated observation kernel.
```

Phase, two quadratures and a calibrated integer readout can have the same kernel. They cannot be counted as several independent unique captures under the intrinsic-information specification. No maximal-root seal or disposition is produced by this batch.

The amplitudes and integral identities are ideal. A single shot is a binary result, so statistical estimation is necessary. The strongest present experimental next step is to include residual endpoint displacement and loss of visibility, then derive a finite-shot decision margin under explicit control uncertainty. A larger phase slope can improve sensitivity while also wrapping the admissible range; the 2026 preprint explicitly discusses this tradeoff. No metrological advantage, QEC performance, measured data or hardware validation is claimed here.

Three parallel self-check processes validated the cocycle and induction identities symbolically, all 2,047 binary words of lengths 0-10 against direct function-action evaluation, and 262,144 sampled golden windows against the range and kernel predictions. The maximum numerical wavefunction discrepancy was below 3.54e-15. These checks are finite self-checks, not Lean verdicts or independent model reviews.

The implementation was authored and reviewed for mathematical logic by the GPT-6 Pro main session. No local Lean toolchain was available. #5750 and its parent remain candidate sources until actually compiled and admitted; no freeze event or merge has been asserted. The existing theory sections are preserved above, and this appendix does not close the geometric-to-valuation problem.

## 30. Library-first statistical audit, 2026-09-06

The finite-shot continuation first audited the repository and related open drafts before introducing any new probability object. The needed statistical machinery was already present in the same #5750 stack:

```text
SymmetricBernoulliProbabilityData
  -> canonical positiveBiasLaw / negativeBiasLaw
FourLocalEvidenceClosedForms
  -> exact symmetric TV and Bhattacharyya formulas
BhattacharyyaExponent
  -> iid testing floors and sample-complexity products
FiniteRepetitionLawKernel
  -> positive finite repetition preserves the one-shot law kernel
FiniteSuiteErrorSqueeze
  -> operational finite-suite optimum and affinity-budget squeeze.
```

Consequently `GoldenFiniteShotVisibility` is a thin physical adapter. It does not define a second Bernoulli family, total variation, Bhattacharyya coefficient, iid product, or Bayes-risk engine. The `FiniteSuiteErrorSqueeze` owner was checked at the actual #5750 head after the write, rather than inferred from a newer `dev` checkout.

The related open draft #4504 was also inspected. It contains a Fourier-Magnus matrix commutator and a free-Lie interpretation of the second-order chronology response. That branch is an adjacent algebraic foundation, not a source to duplicate into the present stochastic-readout stack.

## 31. Visibility is statistical strength with one singular kernel transition

Let the calibrated chronology phase be `2*kappa*m(w)` and define

```text
s_V(w) = V * sin(2*kappa*m(w)),
p_V(w) = (1 + s_V(w)) / 2,
delta_V(w) = s_V(w) / 2.
```

The one-shot readout law is exactly the repository's existing

```text
positiveBiasLaw(delta_V(w)).
```

For `0 <= V <= 1`, the new adapter proves this is valid probability data. The visible fringe is also proved to be the affine contraction

```text
p_V(w) = (1-V)/2 + V * p_ideal(w).
```

There are two qualitatively different regimes.

At `V = 0`, every word has exactly the same one-shot law. The observation kernel jumps to the universal relation and all chronology information disappears from this channel.

For `V > 0`, nonzero `kappa`, and the already-proved no-alias calibration, equality of one-shot laws is equivalent to equality of `magnusCenter`. Thus any two strictly positive visibility values induce the same deterministic indistinguishability relation in the ideal model. They change the distance between distinct laws, not which states are equal under the readout.

This matters for intrinsic-information accounting. Positive visibility settings are not separate deterministic CUTs merely because they produce different numerical probabilities. Their equality kernel is the same calibrated Magnus-center kernel. The singular point `V=0` is a genuine kernel collapse.

Experimental Ramsey work supports treating contrast as a measurable physical quantity rather than a symbolic score. For example, trapped-ion Ramsey data in Rapid exchange cooling with trapped ions report a fitted contrast of 96.0(7)% and binomial confidence intervals on state populations. More recent trapped-ion work on motional-frequency noise uses hundreds of shots per Ramsey point and explicitly separates coherent modulation from contrast loss due to heating. These experiments motivate the visibility and sampling interface. They do not validate the golden-word protocol itself.

## 32. Finite repetition changes confidence, not deterministic information

The repository's frozen `FiniteRepetitionLawKernel` theorem becomes directly applicable after the one-shot law has been identified. For every positive finite shot count `N`, the candidate adapter proves

```text
iidPower(law_V(left), N) = iidPower(law_V(right), N)
  iff
magnusCenter(left) = magnusCenter(right),
```

under positive visibility and the same no-alias premises.

This creates a sharp conceptual separation:

```text
one-shot kernel       -> what is distinguishable in principle
N-shot product law    -> how strongly already-distinct states separate statistically.
```

No finite number of repeated observations can repair a one-shot exact collision. In particular, the odd-length golden collision inherited from the parent module remains a collision under every finite iid repetition. Conversely, when the one-shot laws differ, repetition can amplify statistical evidence without creating a new deterministic coordinate.

Under the v4.3 intrinsic-information specification, an `N`-shot version of the same positive-visibility law should therefore not be counted as a new deterministic kernel refinement merely because its total variation or testing risk changes. Kernel refinement and statistical confidence are different objects.

## 33. Exact one-shot separation and the finite-shot optimal-error squeeze

For a word and its reversal, reversal negates the existing Magnus center. Therefore their visible signals are opposite. The adapter specializes the frozen symmetric-Bernoulli formulas to obtain

```text
TV(law(w), law(reverse(w))) = |s_V(w)|.
```

For `0 <= V < 1`, define

```text
rho(w) = sqrt(1 - s_V(w)^2).
```

Then the exact one-shot Bhattacharyya affinity is

```text
Bhattacharyya(law(w), law(reverse(w))) = rho(w).
```

The recursive `IidSpace` owner gives a universal necessary floor. For every decision event on `N` independent outcomes,

```text
(1 - s_V(w)^2)^N / 2
  <= total two-hypothesis error.
```

Hence total error at most `eps` requires

```text
(1 - s_V(w)^2)^N <= 2 * eps.
```

The repository also contains the independent finite-suite encoding `Fin N -> Outcome` and an operational equal-prior optimum. Specializing that existing owner to `N` identical chronology coordinates gives an attainable Bayes risk `e_N^*`. Its affinity budget reduces exactly to

```text
-N * log(rho).
```

The resulting explicit squeeze is

```text
(1 - sqrt(1 - rho^(2*N))) / 2
  <= e_N^*
  <= rho^N / 2.
```

Therefore

```text
rho^N <= 2 * eps
```

is a sufficient condition for the existing optimal finite-suite decision to achieve equal-prior risk at most `eps`.

The necessary and sufficient interfaces use two already-frozen product encodings. This batch does not pretend they are definitionally identical. A generic equivalence between recursive `IidSpace` and `Fin N -> Outcome`, together with risk transport through that equivalence, would be a reusable estimation theorem and should be proved at the generic owner level if needed.

The present result already closes an important scientific gap from section 29. The model now distinguishes three layers that had previously been conflated:

```text
exact identifiability  -> law kernel
one-shot separation    -> TV / affinity
finite-shot certainty  -> testing risk and sample-count bounds.
```

## 34. Relation to the Fourier-Magnus draft

Open draft #4504 supplies a nearby noncommutative statement: two Fourier-phased matrix channels have a commutator proportional to the second-Magnus swap kernel and to the matrix commutator of the channel generators. Equal times or commuting channel generators kill that response.

The current Weyl lane supplies a different representation of the same structural idea. The binary chronology word accumulates a central Weyl phase whose exponent is `a*b*m(w)`, and reversal doubles the relative phase. The finite-shot module then observes that scalar central character through a Ramsey law.

The next algebraic bridge should therefore have the shape

```text
second-Magnus / free-Lie bracket coordinate
  -> evaluate in a concrete Weyl representation
  -> central phase exponent
  -> Ramsey probability law.
```

This bridge is not yet claimed. It requires reconciling the two open branches on a common base and proving the representation map, rather than copying declarations from #4504 into #5750. If successful, it would identify the matrix/free-Lie chronology owner and the scalar interferometric owner as two representations of one second-order noncommutative invariant.

## 35. Next experimental boundary: uncertain contrast, offset, and correlated drift

The current visibility model assumes a calibrated contrast `V`, a centered fringe with baseline one half, independent repeated shots, and exact endpoint closure. Real Ramsey measurements can contain phase offsets, slowly drifting detuning, imperfect contrast calibration, and heating-induced loss of coherence. The 2026 trapped-ion motional-frequency study explicitly models coherent sinusoidal frequency modulation together with a heating envelope and reports shot-noise error bars from 500 measurements per point.

The next useful theorem should therefore be robust rather than decorative. A candidate observation model is

```text
p(w) = c + V * sin(2*kappa*m(w) + theta) / 2,
```

with certified intervals for `c`, `V`, and `theta`, plus an explicit residual endpoint-displacement error. The research question is then whether two legal golden factors remain uniformly separated over the entire admissible calibration set.

The desired conclusion has two levels:

1. a robust deterministic statement that interval uncertainty does or does not preserve the center kernel on a specified finite golden window;
2. a finite-shot statistical statement giving a confidence-controlled decision margin after the worst-case contraction of the Bernoulli separation.

The repository already contains binomial KL-Chernoff tails, generic divergence testing bounds, and exact finite-suite optimal-error machinery. Those owners should be consumed before any new concentration inequality is written. The first unresolved task is to identify the smallest generic interval-uncertainty primitive that can express visibility, offset, phase calibration, and residual path closure without turning four physical errors into four ad hoc scores.

The current candidate source for sections 30-35 is #5750 at `047738154d1c31712c397075183b64fbc551df5f`. It remains logically reviewed source without a local Lean compilation verdict. No frozen-state or admission claim is made here.

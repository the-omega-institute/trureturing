# Spectral Dynamics Toward Weil Positivity

## Abstract

Coefficient dynamics and zero resonance align spectral geometry on the O-6 path.

**Theorem 1.1 (Vertical evolution is a norm-preserving group).**

$$\forall t,u\in\mathbb{R},\ \forall x\in\operatorname{ZetaHilbertSpace},\ V_{0}x=x \land V_{t+u}x=V_{t}(V_{u}x) \land V_{-t}(V_{t}x)=x \land \Vert V_{t}x\Vert=\Vert x\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

Multiplication of each coefficient by n to the power -it gives the identity, composition, inverse, and norm-preservation laws on the square-summable coefficient space. The declaration proves those laws directly for the coordinate multiplier; it does not introduce an unbounded self-adjoint length operator, bundle a continuous linear unitary equivalence, or prove strong continuity or a generator theorem.

**Theorem 1.2 (Forward horizontal evolution is a contraction semigroup).**

$$\forall \delta,\varepsilon\in\mathbb{R},\ \delta\geq 0 \land \varepsilon\geq 0 \Rightarrow \forall x\in\operatorname{ZetaHilbertSpace},\ H_{0}x=x \land H_{\delta+\varepsilon}x=H_{\delta}(H_{\varepsilon}x) \land \Vert H_{\delta}x\Vert\leq\Vert x\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralDynamics.horizontal_evolution_contraction_semigroup` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

For nonnegative real increments, multiplication of the nth coefficient by n to the power -delta gives identity and composition laws and cannot increase the square-summable norm. Only this bounded forward direction is bundled. The declaration does not define the reverse unbounded operator or characterize the domain of a multiplier by n to the power delta.

**Theorem 1.3 (Labeled zeta vectors follow the coordinate evolutions).**

$$\forall \sigma,\sigma',t\in\mathbb{R},\ \frac{1}{2}<\sigma \land \sigma\leq\sigma' \Rightarrow V_{t}\operatorname{labeledZetaVector}(\sigma)=\operatorname{labeledZetaVector}(\sigma+it) \land H_{\sigma'-\sigma}\operatorname{labeledZetaVector}(\sigma+it)=\operatorname{labeledZetaVector}(\sigma'+it)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralDynamics.labeled_zeta_evolution_spec` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

A labeled zeta vector to the right of the half-density boundary is carried from sigma to sigma + it by the vertical multiplier. If sigma is at most sigma prime, the bounded horizontal multiplier then carries it to sigma prime + it. The ordering hypothesis makes the source's forward dissipative direction explicit; no reverse-domain identity is asserted.

**Theorem 1.4 (Zero symmetries form the kernel-resonant cross-pairs).**

$$\forall Z:\operatorname{ZeroData},\ \forall n\in\mathbb{N},\ Z_{C(R(n))}=1-\overline{Z_{n}} \land \operatorname{KernelResonant}(Z_{n},Z_{C(R(n))}) \land \operatorname{KernelResonant}(Z_{C(n)},Z_{R(n)}) \land (\forall w,\ \operatorname{KernelResonant}(Z_{n},w) \Leftrightarrow w=Z_{C(R(n))})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing reflection and conjugation permutations send every enumerated nontrivial zero to its unique partner for the equation s plus conjugate w equals one, and the two cross-pairs satisfy that equation. The declaration is conditional on a supplied ZeroData value. The repository does not prove that ZeroData is inhabited: no instance or example exists. Accordingly this conditional theorem does not close the source corollary unconditionally; that source obligation remains open. This strengthens the conditional conclusion from off-line zeros to all enumerated zeros, so it permits degenerate critical-line configurations and asserts no pairwise distinct quartet. Resonance here is only the kernel equation, not a new analytic pole or continuation theorem.

**Theorem 1.5 (Critical-line predicates use one abscissa).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ (\exists a,\ell(a)\neq 0) \Rightarrow \forall s\in\mathbb{C},\ (s=\operatorname{mirror}(s)\Leftrightarrow\Re(s)=\frac{1}{2}) \land ((\forall a,\Vert\operatorname{halfDensityReading}(\ell,s,a)\Vert=1)\Leftrightarrow\Re(s)=\frac{1}{2}) \land (s+\overline{s}=1\Leftrightarrow\Re(s)=\frac{1}{2}) \land (\operatorname{MemLp}(\operatorname{labeledZetaCoefficient}(s),2)\Leftrightarrow\frac{1}{2}<\Re(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/SpectralDynamics.critical_line_characterizations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any additive ledger with a nonzero length, mirror fixed points, unit-modulus half-density readings, and self-resonance all select real part one half. The labeled zeta coefficient is square-summable exactly on the strict right half-plane, exposing one half as its boundary without asserting endpoint membership. The combined statement locates no zeta zero and adds no Riemann-hypothesis conclusion.

**Remark 1.6 (Diagonal flow and the generator boundary).**

Lean statement: `D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group`

*Formalization.* `D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate multiplier has logarithmic frequencies, but the checked declaration supplies only its group and norm laws. It does not construct a self-adjoint operator whose spectrum is the zeta zeros; that Hilbert-Polya step remains outside this module.

**Remark 1.7 (Two regimes and two directions).**

Lean statement: `D5/S3/Weil/SpectralDynamics.critical_line_characterizations`

*Formalization.* `D5/S3/Weil/SpectralDynamics.critical_line_characterizations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The square-summable side is the strict half-plane to the right of one half. Vertical evolution is reversible and norm-preserving, while the formal horizontal evolution is only a forward contraction. Reading these as two phases or two times is a narrative synthesis, not a functional equation or a zero-location theorem.

**Remark 1.8 (Phase delay is not address delay).**

Lean statement: `D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group`

*Formalization.* `D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertical multiplier records reversible phase accumulation. A discrete walk needed to reach an address is a different notion of delay, and this declaration neither identifies the two nor assigns an intrinsic time offset between parallel coefficient flows.

**Remark 1.9 (Off-line pairs remain conditional).**

Lean statement: `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec`

*Formalization.* `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For supplied zero data, mirror and conjugation organize entries into the checked cross-pairs. The declaration does not establish that such data exists, that an off-line entry occurs, or that a paired entry has decay, lifetime, or probabilistic meaning.

**Remark 1.10 (Counting does not locate real parts).**

Lean statement: `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec`

*Formalization.* `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional partner equations preserve the supplied inventory but do not determine the real coordinate of any entry. Argument-principle counts, collision dynamics, and the existence of zero data are separate obligations not discharged here.

**Remark 1.11 (Equalities do not supply positivity).**

Lean statement: `D5/S3/Weil/SpectralDynamics.critical_line_characterizations`

*Formalization.* `D5/S3/Weil/SpectralDynamics.critical_line_characterizations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Symmetry equations and the shared half-density coordinate do not imply Li or Weil positivity and therefore do not locate zeros. Metaphors that separate reversible phase time from irreversible ledger time remain explanatory readings rather than additional formal conclusions.

**Remark 1.12 (Speculative off-line effects are not formalized).**

Lean statement: `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec`

*Formalization.* `D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checked zero-data result records only permutations and resonance equations. Detection scales, thermal lifetimes, causal effects on prime counting, and physical interpretations of hypothetical off-line entries are not claims of this module.

**Remark 1.13 (Thermal time is a meta-time, not a physical history).**

$$
H_{0} = \mathit{Xi}
$$

*Source.* Repository-derived.

*Commentary.*

Three ingredients explain the source's thermal imagery. First, the Connes-Rovelli thermal-time hypothesis identifies physical time with the modular flow generated by a state; the source treats its de Bruijn-Newman time as an arithmetic analogue and notes that modular flow is also the Bost-Connes time evolution associated there with unitary scaling. Second, it offers only a heuristic that critical physical systems exhibit universal fluctuations, random-matrix statistics are a standard universality class, and GUE zero statistics might therefore be related to the critical value Lambda = 0. That relation is marked unproved. Third, the source supplies the limiting correction: de Bruijn-Newman time parametrizes a family of systems rather than the physical evolution of one system. H_0 = Xi is the actual object by definition, while t > 0 gives mathematical deformations. The claimed present moment is therefore the name of the undeformed system, not evidence that a universe selected one time on the heat axis.

**Remark 1.14 (Causal direction requires irreversible bookkeeping).**

$$
\mathit{causality} = \mathit{logic} \cdot \mathit{irreversibility}
$$

*Source.* Repository-derived.

*Commentary.*

The source presents an internal self-model in which evolution factors into orthogonal operations, classification, and bookkeeping. It assigns new axes to orthogonal pairing and convolution, two complementary halves to classification, and the growth of the ledger to time; this description is expressly not claimed for the external world. It then corrects the slogan that logic alone gives causality. Logic has no tense and reversible phase time has no arrow; causal direction appears only in the ledger layer, fueled by monotone cost. Hence its formula is causality = logic * irreversibility, with a minimal demonstration in which the same rule has a directionless period-two reversible implementation but a strictly growing bookkeeping implementation that orders events. Finally, the Pythagorean claim that everything is number is classified as a normative choice rather than a truth-valued proposition. The internal kernel may be considered a self-contained universe model, but whether the external world is that model is kept outside the classification scheme and deliberately left undecided.

## References

- Dependency: [D5/S3/Weil/CriticalLine](CriticalLine.md)
- Dependency: [D5/S3/Weil/SpectralHilbert](SpectralHilbert.md)

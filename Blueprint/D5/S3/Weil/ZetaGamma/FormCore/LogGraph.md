# The original Gamma graph and the logarithmic Fourier domain

## Abstract

The actual Gamma jump graph and PLUS log Fourier square norm on arbitrary complex Ioc L2 profiles.

**Definition 1.1 (The zero-frequency digamma value).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.d0`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.d0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d0 is the real part of digamma at 1/4.

**Definition 1.2 (The positive logarithmic weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.ell`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t, ell(t)=log(|t|+3). The weight is continuous and at least one.

**Definition 1.3 (The lower comparison constant).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C1`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C1=|d0|+5+log(5) is the constant in ell(t)<=C1*(1+delta(t)).

**Definition 1.4 (The upper comparison constant).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C2`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C2=6+|d0| is the constant in delta(t)<=C2*ell(t).

**Definition 1.5 (The extended PLUS logarithmic mass).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.logFourierMass`

*Formalization.* `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.logFourierMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex function f on the real line, logFourierMass(f) is the nonnegative extended integral of ofReal(ell(t))*enorm(paperFT(f,t))^2 with respect to Lebesgue measure. Finiteness is not part of its definition.

**Theorem 1.6 (Explicit scalar constants on the entire frequency line).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_scalar_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_scalar_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write d0=Re digamma(1/4), delta(t)=Re digamma(1/4+i*t/2)-d0, ell(t)=log(|t|+3), C1=|d0|+5+log(5), and C2=6+|d0|. For every real t the theorem gives delta(t)>=0, delta(-t)=delta(t), ell(t)<=C1*(1+delta(t)), and delta(t)<=C2*ell(t).

Nonnegativity is reused from the actual Levy multiplier theorem; evenness uses the actual mu-even theorem and its exact digamma dictionary. For |t|<=2 the compact-frequency bound bounds the n=0 series term by 64/17 and the complete remaining tail by 2, so delta(t)<=98/17<6. For |t|>=2, Zeta23.StirlingVert.re_digamma_stirling' is applied with imaginary parameter t/2: the error is at most 5/(t/2)^2=20/t^2<=5. The comparison |t|+3<=5*|t|/2 supplies the exact log(5) in C1. There is no unspecified compact supremum or omitted zero series term.

**Theorem 1.7 (The actual measure and the extended PLUS estimates).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex whole-line function f with Integrable f and MemLp f 2, let M2=coreL2Mass f and E=directionalEnergy actualGammaExitMeasure f. Both are the existing nonnegative integrals. Let H=M2+E and L=integral ell(t)*|paperFT f(t)|^2, interpreted first in ENNReal. The four conclusions are E=(1/(2*pi))*integral delta(t)*|paperFT f(t)|^2, M2=(1/(2*pi))*integral |paperFT f(t)|^2, L<=2*pi*C1*H, and H<=((1+C2)/(2*pi))*L. Every displayed integral in these four conclusions is extended and may equal infinity.

The measure's Corner.actualDensity and LineFourier.actualDensity both unfold to the archimedeanJumpDensity. The theorem first proves each L2 displacement has an integrable squared norm, then uses the withDensity formula. A measurable representative is used for the product integral and transported back by the existing directionalEnergy AE invariance and pointwise integral Fourier invariance. The existing whole-line Levy/Plancherel theorem is consumed, not duplicated.

paperFT f(t)=angularFourier f(-t), because paperFT has the PLUS exponent and the angular transform has the negative exponent. Lebesgue reflection and actual delta evenness pay the sign change. The input function is arbitrary complex, with no conjugation, evenness or reality assumption. Nonnegative integration of the scalar inequalities pays both constants before any finite-energy restriction.

**Theorem 1.8 (The maximal finite jump domain inside L1 intersect L2).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_finite_energy_iff_log_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_finite_energy_iff_log_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same whole-line L1 and L2 assumptions, actual jump energy is finite if and only if the ordinary real function ell(t)*|paperFT f(t)|^2 is Integrable. The forward implication bounds its nonnegative integral by a finite graph mass; the reverse implication bounds graph mass by the finite logarithmic integral. Continuous raw Fourier representatives supply measurability. The theorem does not assume finite energy in its premise and does not identify two totalized divergent real integrals.

**Theorem 1.9 (Ordinary estimates after finiteness has been paid).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_real_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_real_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Integrable f, MemLp f 2 and actual jump energy E<infinity. The theorem returns ordinary log-weight integrability and the two real inequalities integral ell*|paperFT f|^2<=2*pi*C1*(integral |f|^2+E.toReal) and integral |f|^2+E.toReal<=((1+C2)/(2*pi))*integral ell*|paperFT f|^2. The existing L2 mass is finite, and all uses of toReal order and sum conversion are guarded. This is the real-number consumer of the extended theorem, not a definition of energy by a spectral replacement.

**Theorem 1.10 (Attach the actual half-open spatial carrier).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_graph_log_equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_graph_log_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real a and complex u with MemLp u 2 on volume restricted to Ioc(-a,a), F is literally PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. The endpoint identity -a+2*a=a is used exactly: F excludes the left endpoint and includes the right endpoint when a>0. Finite interval measure supplies L1 and the existing indicator theorem supplies L2. The theorem gives both extended estimates and the iff between actual jump energy finiteness and log-weight Integrable. The intended nondegenerate application fixes a>0, but the statement also keeps degenerate intervals. No trace condition, smoothness, parity or real-valued restriction is introduced. The smooth compact core applies to every such complex profile of finite actual energy.

**Theorem 1.11 (Original differences and approximation errors).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_difference_graph_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_difference_graph_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two arbitrary complex Ioc L2 profiles u,v on the same fixed window, let F,G be their literal zero extensions and e=F-G. The theorem retains the exact identity coreL2Mass(e)=integral over Ioc(-a,a) of |u-v|^2, both extended graph/log estimates for e, proves the pointwise real-frequency identity paperFT e=paperFT F-paperFT G, and states the finite-domain iff with the latter difference inside the logarithmic square. It uses LineFourier.raw_fourier_sub with the required L1 hypotheses. Neither profile is silently replaced by an even part or by a periodic lift.

For a finite-energy complex profile u on Ioc(-a,a), apply actual_ioc_exists_smooth_compact_core_approximation at any positive tolerance epsilon. It gives a smooth compact H supported inside Ioo(-a,a) whose actual graph error is less than ofReal(epsilon). The extended graph estimate then bounds the logFourierMass of H minus the literal zero extension by ofReal(2*pi*C1)*ofReal(epsilon). The existing coreL2Mass_error_eq_original_ioc identifies its mass with the exact restricted Ioc error integral. The error has finite actual energy, so the ordinary log-weight square integral is integrable. This application retains arbitrary complex profiles and the original half-open endpoints.

**Theorem 1.12 (Exact dictionary for the existing continuity weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_dictionary`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_dictionary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With w(t)=1+log(1+|t|), every real t satisfies ell(t)<=log(3)*w(t) and w(t)<=2*ell(t). The elementary lower logarithm inequality at x=2 gives log(3)>=1; logarithmic monotonicity gives the remaining comparisons. These explicit constants translate the current graph weight to the exact private weight appearing in the public LogarithmicFormContinuity consumer. No private declaration from that module is called or promoted.

**Theorem 1.13 (The same integrable frequency domain for both weights).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_integrable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_integrable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous complex frequency profile P, Integrable of ell(t)*norm(P(t))^2 is equivalent to Integrable of (1+log(1+|t|))*Complex.normSq(P(t)). Both directions use the explicit weight comparisons, continuous measurability, nonnegativity and domination. The norm-square versus normSq equality and constants are explicit, so the result can be applied directly to the existing public continuity theorem without rewriting that theorem's analytic proof.

**Theorem 1.14 (Consume the existing actual Gamma quadratic continuity theorem).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_quadratic_tendsto_of_graph_error`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_quadratic_tendsto_of_graph_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let l be any filter, u an original Ioc L2 target of finite actual jump energy, and v(i) a family of Ioc L2 profiles on the SAME window. Assume the existing extended coreGraphSize of their zero-extension errors tends to zero. The theorem concludes convergence of the actual normalized quadratic integrals with symbol 2*pi*Zeta23.mu and frequency profiles paperFT of the zero extensions.

Extended convergence makes the graph errors <1 eventually, hence the actual error energies finite eventually. The real graph estimate and w<=2*ell give (1/(2*pi))*integral w*|paperFT(error)|^2 <=2*C1*coreGraphSize(error).toReal. Continuity of toReal at zero and this bound give exactly the weighted-error limit. Raw Fourier continuity, target weighted integrability and eventual error weighted integrability discharge all remaining hypotheses. The last proof line applies LogarithmicFormContinuity.actual_gamma_quadratic_tendsto_of_log_weight_error. Its private growth helper and mixed-term analysis are not redeveloped.

The conclusion concerns this actual Gamma quadratic form. It does not assert convergence of the other terms of an explicit formula.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C1`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.C2`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_finite_energy_iff_log_integrable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_bounds`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_graph_log_real_bounds`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_gamma_scalar_bounds`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_difference_graph_log_bounds`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_graph_log_equivalence`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.actual_ioc_gamma_quadratic_tendsto_of_graph_error`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.d0`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.ell`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.logFourierMass`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_dictionary`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/LogGraph.log_weight_integrable_iff`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy](PeriodicSpectralEnergy.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/SmoothCore](SmoothCore.md)
- Dependency: [D5/S3/Weil/ZetaGamma/LogarithmicFormContinuity](../LogarithmicFormContinuity.md)

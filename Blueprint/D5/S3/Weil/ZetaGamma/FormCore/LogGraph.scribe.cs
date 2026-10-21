using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class LogGraphDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/LogGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Gamma jump graph and PLUS log Fourier square norm on arbitrary complex Ioc L2 profiles.",
        H("The original Gamma graph and the logarithmic Fourier domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-graph-definition-d0"),
                DeclarationHandle.Create(Owner + "d0"),
                H("The zero-frequency digamma value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("d0 is the real part of digamma at 1/4."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-graph-definition-ell"),
                DeclarationHandle.Create(Owner + "ell"),
                H("The positive logarithmic weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real t, ell(t)=log(|t|+3). The weight is continuous and at least one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-graph-definition-c1"),
                DeclarationHandle.Create(Owner + "C1"),
                H("The lower comparison constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C1=|d0|+5+log(5) is the constant in ell(t)<=C1*(1+delta(t))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-graph-definition-c2"),
                DeclarationHandle.Create(Owner + "C2"),
                H("The upper comparison constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C2=6+|d0| is the constant in delta(t)<=C2*ell(t)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-graph-definition-logfouriermass"),
                DeclarationHandle.Create(Owner + "logFourierMass"),
                H("The extended PLUS logarithmic mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary complex function f on the real line, logFourierMass(f) is the nonnegative extended integral of ofReal(ell(t))*enorm(paperFT(f,t))^2 with respect to Lebesgue measure. Finiteness is not part of its definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-explicit-scalar-log-bounds"),
                DeclarationHandle.Create(Owner + "actual_gamma_scalar_bounds"),
                H("Explicit scalar constants on the entire frequency line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write d0=Re digamma(1/4), delta(t)=Re digamma(1/4+i*t/2)-d0, "
                        + "ell(t)=log(|t|+3), C1=|d0|+5+log(5), and C2=6+|d0|. "
                        + "For every real t the theorem gives delta(t)>=0, delta(-t)=delta(t), "
                        + "ell(t)<=C1*(1+delta(t)), and delta(t)<=C2*ell(t).")),
                    Paragraph(Text(
                        "Nonnegativity is reused from the actual Levy multiplier theorem; evenness "
                        + "uses the actual mu-even theorem and its exact digamma dictionary. "
                        + "For |t|<=2 the compact-frequency bound bounds the n=0 series term by 64/17 "
                        + "and the complete remaining tail by 2, so delta(t)<=98/17<6. For |t|>=2, "
                        + "Zeta23.StirlingVert.re_digamma_stirling' is applied with imaginary "
                        + "parameter t/2: the error is at most 5/(t/2)^2=20/t^2<=5. "
                        + "The comparison |t|+3<=5*|t|/2 supplies the exact log(5) in C1. "
                        + "There is no unspecified compact supremum or omitted zero series term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-extended-plus-graph-log-bounds"),
                DeclarationHandle.Create(Owner + "actual_gamma_graph_log_bounds"),
                H("The actual measure and the extended PLUS estimates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any complex whole-line function f with Integrable f and MemLp f 2, "
                        + "let M2=coreL2Mass f and E=directionalEnergy actualGammaExitMeasure f. "
                        + "Both are the existing nonnegative integrals. Let H=M2+E and "
                        + "L=integral ell(t)*|paperFT f(t)|^2, interpreted first in ENNReal. "
                        + "The four conclusions are E=(1/(2*pi))*integral delta(t)*|paperFT f(t)|^2, "
                        + "M2=(1/(2*pi))*integral |paperFT f(t)|^2, L<=2*pi*C1*H, "
                        + "and H<=((1+C2)/(2*pi))*L. Every displayed integral in these four "
                        + "conclusions is extended and may equal infinity.")),
                    Paragraph(Text(
                        "The measure's Corner.actualDensity and LineFourier.actualDensity "
                        + "both unfold to the archimedeanJumpDensity. The theorem "
                        + "first proves each L2 displacement has an integrable squared norm, then "
                        + "uses the withDensity formula. A measurable representative is used for "
                        + "the product integral and transported back by the existing directionalEnergy "
                        + "AE invariance and pointwise integral Fourier invariance. The existing "
                        + "whole-line Levy/Plancherel theorem is consumed, not duplicated.")),
                    Paragraph(Text(
                        "paperFT f(t)=angularFourier f(-t), because paperFT has the PLUS exponent "
                        + "and the angular transform has the negative exponent. Lebesgue reflection "
                        + "and actual delta evenness pay the sign change. The input function is "
                        + "arbitrary complex, with no conjugation, evenness or reality assumption. "
                        + "Nonnegative integration of the scalar inequalities pays both constants "
                        + "before any finite-energy restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-finite-domain-iff-log-integrable"),
                DeclarationHandle.Create(Owner + "actual_gamma_finite_energy_iff_log_integrable"),
                H("The maximal finite jump domain inside L1 intersect L2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same whole-line L1 and L2 assumptions, actual jump energy is "
                    + "finite if and only if the ordinary real function ell(t)*|paperFT f(t)|^2 "
                    + "is Integrable. The forward implication bounds its nonnegative integral "
                    + "by a finite graph mass; the reverse implication bounds graph mass by the "
                    + "finite logarithmic integral. Continuous raw Fourier representatives supply "
                    + "measurability. The theorem does not assume finite energy in its premise "
                    + "and does not identify two totalized divergent real integrals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-guarded-real-graph-log-bounds"),
                DeclarationHandle.Create(Owner + "actual_gamma_graph_log_real_bounds"),
                H("Ordinary estimates after finiteness has been paid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume Integrable f, MemLp f 2 and actual jump energy E<infinity. "
                    + "The theorem returns ordinary log-weight integrability and the two real "
                    + "inequalities integral ell*|paperFT f|^2<=2*pi*C1*(integral |f|^2+E.toReal) "
                    + "and integral |f|^2+E.toReal<=((1+C2)/(2*pi))*integral ell*|paperFT f|^2. "
                    + "The existing L2 mass is finite, and all uses of toReal order and sum "
                    + "conversion are guarded. This is the real-number consumer of the extended "
                    + "theorem, not a definition of energy by a spectral replacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-original-ioc-gamma-log-equivalence"),
                DeclarationHandle.Create(Owner + "actual_ioc_gamma_graph_log_equivalence"),
                H("Attach the actual half-open spatial carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real a and complex u with MemLp u 2 on volume restricted to "
                    + "Ioc(-a,a), F is literally PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. "
                    + "The endpoint identity -a+2*a=a is used exactly: F excludes the left endpoint and includes the right endpoint when a>0. "
                    + "Finite interval measure supplies L1 and the existing indicator theorem "
                    + "supplies L2. The theorem gives both extended estimates and the iff "
                    + "between actual jump energy finiteness and log-weight Integrable. The "
                    + "intended nondegenerate application fixes a>0, but the statement also keeps "
                    + "degenerate intervals. No trace condition, smoothness, parity or real-valued "
                    + "restriction is introduced. The smooth compact core applies to every such complex profile of finite actual energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-original-ioc-difference-log-graph-bounds"),
                DeclarationHandle.Create(Owner + "actual_ioc_difference_graph_log_bounds"),
                H("Original differences and approximation errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two arbitrary complex Ioc L2 profiles u,v on the same fixed window, "
                    + "let F,G be their literal zero extensions and e=F-G. The theorem retains "
                    + "the exact identity coreL2Mass(e)=integral over Ioc(-a,a) of |u-v|^2, "
                    + "both extended graph/log estimates for e, proves the pointwise real-frequency "
                    + "identity paperFT e=paperFT F-paperFT G, and states the finite-domain iff "
                    + "with the latter difference inside the logarithmic square. It uses "
                    + "LineFourier.raw_fourier_sub with the required L1 hypotheses. Neither "
                    + "profile is silently replaced by an even part or by a periodic lift."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a finite-energy complex profile u on Ioc(-a,a), apply "
                + "actual_ioc_exists_smooth_compact_core_approximation at any positive tolerance epsilon. "
                + "It gives a smooth compact H supported inside Ioo(-a,a) whose actual graph error "
                + "is less than ofReal(epsilon). The extended graph estimate then bounds the "
                + "logFourierMass of H minus the literal zero extension by "
                + "ofReal(2*pi*C1)*ofReal(epsilon). The existing "
                + "coreL2Mass_error_eq_original_ioc identifies its mass with the exact restricted "
                + "Ioc error integral. The error has finite actual energy, so the ordinary "
                + "log-weight square integral is integrable. This application retains arbitrary "
                + "complex profiles and the original half-open endpoints.")),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-weight-exact-dictionary"),
                DeclarationHandle.Create(Owner + "log_weight_dictionary"),
                H("Exact dictionary for the existing continuity weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With w(t)=1+log(1+|t|), every real t satisfies ell(t)<=log(3)*w(t) "
                    + "and w(t)<=2*ell(t). The elementary lower logarithm inequality at x=2 "
                    + "gives log(3)>=1; logarithmic monotonicity gives the remaining comparisons. "
                    + "These explicit constants translate the current graph weight to the exact "
                    + "private weight appearing in the public LogarithmicFormContinuity consumer. "
                    + "No private declaration from that module is called or promoted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-log-weight-integrable-dictionary"),
                DeclarationHandle.Create(Owner + "log_weight_integrable_iff"),
                H("The same integrable frequency domain for both weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every continuous complex frequency profile P, Integrable of "
                    + "ell(t)*norm(P(t))^2 is equivalent to Integrable of "
                    + "(1+log(1+|t|))*Complex.normSq(P(t)). Both directions use the explicit "
                    + "weight comparisons, continuous measurability, nonnegativity and domination. "
                    + "The norm-square versus normSq equality and constants are explicit, so "
                    + "the result can be applied directly to the existing public continuity "
                    + "theorem without rewriting that theorem's analytic proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-original-ioc-gamma-quadratic-from-graph-error"),
                DeclarationHandle.Create(Owner + "actual_ioc_gamma_quadratic_tendsto_of_graph_error"),
                H("Consume the existing actual Gamma quadratic continuity theorem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let l be any filter, u an original Ioc L2 target of finite actual jump "
                        + "energy, and v(i) a family of Ioc L2 profiles on the SAME window. "
                        + "Assume the existing extended coreGraphSize of their zero-extension "
                        + "errors tends to zero. The theorem concludes convergence of the "
                        + "actual normalized quadratic integrals with symbol 2*pi*Zeta23.mu "
                        + "and frequency profiles paperFT of the zero extensions.")),
                    Paragraph(Text(
                        "Extended convergence makes the graph errors <1 eventually, hence the "
                        + "actual error energies finite eventually. The real graph estimate and "
                        + "w<=2*ell give (1/(2*pi))*integral w*|paperFT(error)|^2 "
                        + "<=2*C1*coreGraphSize(error).toReal. Continuity of toReal at zero "
                        + "and this bound give exactly the weighted-error limit. Raw Fourier "
                        + "continuity, target weighted integrability and eventual error weighted "
                        + "integrability discharge all remaining hypotheses. The last proof line "
                        + "applies LogarithmicFormContinuity.actual_gamma_quadratic_tendsto_of_log_weight_error. "
                        + "Its private growth helper and mixed-term analysis are not redeveloped.")),
                    Paragraph(Text(
                        "The conclusion concerns this actual Gamma quadratic form. It does not assert convergence of the other terms of an explicit formula."))),
                DescribeRole.Theorem))));
}
